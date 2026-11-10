import LicUpd.K1

/-!
# LicUpd — K2, K4, K5, K6

- **K2** (`k2_derivable`): a getter of a getter. In K2's world, the second image at `ℓ₂` is
  derivable from the start's flattening through the first image at `ℓ₁`, both at `{α}`.
  Together with `UpdVLic.trans` (`Lic.lean`), two G1 runs compose. No lemma is needed per
  depth.
- **K4** (`k4_refused`, `k4_mutExempt_admits`): G1 does not exempt a `mut` cell. A run that
  changes a `mut` cell's predicate is refused by `UpdVLic`. A `mut` exemption, which is what G2
  as written amounts to, admits it.
- **K5** (`k5_own_image_undefined`): `own(v) ● imm(t, v, w)` at one location is undefined. So
  a lend's end cannot restore `own` while an image of the same location stays in the garbage,
  and an absorption step is needed at the end.
- **K6** (`not_g2ThenG1Compose`): G2 read off a run's start (`¬ HoldsAll`) does not compose.
  The chain is: the token leaves, then G2 conjures the lent cell, then G1 derives a getter's
  image. Every step is admitted, and the composite is not.
-/

noncomputable section

namespace BoCa.Fig16.LicUpd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-! ### K2: a getter of a getter -/

/-- **K2.** A view `imm(s, loc ℓ₁, R)` of `σ` at `m`, with `α ∈ s`, `R(ℓ₁) = own(loc ℓ₂)`, and
the first image's witness `w₁ ≤ R` owning `ℓ₂`. Then the second image `imm({α}, u, ∅)` at `ℓ₂`
is derivable from `σ`. -/
theorem k2_derivable {σ : WRes} {m l₁ l₂ : Loc} {s : LSet} {R w₁ : WRes}
    {hR : R.InStratum s.join} {α : Life} {u : Val}
    (hw₁ : w₁.InStratum (LSet.singleton α).join)
    (e : σ.get m = some (CellU.immOf s (Val.loc l₁) R hR)) (hαs : s.mem α)
    (h₁ : R.get l₁ = some (CellU.ownOf (Val.loc l₂))) (hle₁ : ResU.Le w₁ R)
    (h₂ : w₁.get l₂ = some (CellU.ownOf u)) :
    Derivable σ l₂ (CellU.immOf (LSet.singleton α) u PMap.empty
      (inStratum_emptyW _)) := by
  have d₁ : Derivable σ l₁ (CellU.immOf (LSet.singleton α) (Val.loc l₂) w₁ hw₁) :=
    Derivable.proj (Derivable.base e rfl) h₁
      (fun x hx => ⟨x, by rw [show x = α from hx]; exact hαs, le_refl x⟩) hle₁
  exact Derivable.proj d₁ h₂ (fun x hx => ⟨x, hx, le_refl x⟩) ⟨w₁, ResU.comp_empty_left _⟩

/-- **K2 at the world level.** Two G1 runs, the first deriving `ℓ₁`'s image and the second
`ℓ₂`'s from it, compose. -/
theorem k2_compose {ρ₀ ρ₁ ρ₂ : WRes} (h₁ : UpdVLic ρ₀ ρ₁) (h₂ : UpdVLic ρ₁ ρ₂) :
    UpdVLic ρ₀ ρ₂ :=
  h₁.trans h₂

/-! ### K4: a `mut` cell's predicate -/

/-- **K4.** G1 refuses a run whose `mut` cell changes its predicate `P̂` to `Q̂`. -/
theorem k4_refused {l : Loc} {b : Life} {v : Val} {ρw : WRes} {hρ : ρw.InStratum b}
    {P Q : Val → SPropS Loc Val b} {hP : P v ⟨ρw, hρ⟩} {hQ : Q v ⟨ρw, hρ⟩} (hPQ : P ≠ Q) :
    ¬ UpdVLic (ResU.single l (CellU.mutOf b v ρw hρ P hP))
      (ResU.single l (CellU.mutOf b v ρw hρ Q hQ)) := by
  rintro ⟨⟨-, hmut⟩, -, ⟨σπ, hσπ⟩⟩
  have hπ := flat_single_get_of_ne_imm (by simp) hσπ
  obtain ⟨v', χ', h', hw', σ', hσ', e'⟩ := (hmut l b Q).mpr ⟨v, ρw, hρ, hQ, σπ, hσπ, hπ⟩
  rw [flat_single_get_of_ne_imm (by simp) hσ'] at e'
  exact hPQ (CellU.mutOf_inj (Option.some.inj e')).2.2

/-- `↭`'s `mut` clause outside a set `E` of exempt locations. -/
def UpdMutE (E : Loc → Prop) (ρ₁ ρ₂ : WRes) : Prop :=
  ∀ l, ¬ E l → ∀ (b : Life) (P : Val → SPropS Loc Val b),
    (∃ (v : Val) (χ : WRes) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
        ρ₁.FlatAt l (CellU.mutOf b v χ h P hw)) ↔
    (∃ (v : Val) (χ : WRes) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
        ρ₂.FlatAt l (CellU.mutOf b v χ h P hw))

/-- **K4, the other side.** G2 as written exempts every location of a lifetime whose token the
run does not hold, `mut` clause included. Here every location belongs to it, and the exemption
admits the predicate change that `k4_refused` refuses. -/
theorem k4_mutExempt_admits {l : Loc} {b : Life} {v : Val} {ρw : WRes} {hρ : ρw.InStratum b}
    {P Q : Val → SPropS Loc Val b} {hP : P v ⟨ρw, hρ⟩} {hQ : Q v ⟨ρw, hρ⟩} :
    UpdMutE (fun _ => True) (ResU.single l (CellU.mutOf b v ρw hρ P hP))
      (ResU.single l (CellU.mutOf b v ρw hρ Q hQ)) :=
  fun _ hx => absurd trivial hx

/-! ### K5: an image next to the owner it came from -/

/-- **K5.** `ℓ ↦ own(v) ● ℓ ↦ imm(t, v, w)` is undefined. -/
theorem k5_own_image_undefined {l : Loc} {v : Val} {t : LSet} {w : WRes}
    {hw : w.InStratum t.join} :
    ¬ ∃ W, ResU.CompS (ResU.single l (CellU.ownOf v)) (ResU.single l (CellU.immOf t v w hw)) W := by
  rintro ⟨W, hW⟩
  obtain ⟨s₁, s₂, v', ρ', h₁, h₂, e₁, -⟩ :=
    hW.1 l _ _ (ResU.single_get_self _ _) (ResU.single_get_self _ _)
  exact CellU.ownOf_ne_immOf e₁

/-! ### K6: G2 read off a run's start -/

/-- A resource with one lifetime token: `tok` says whether the resource holds `[α]_1` for
the one lifetime `α` every location here belongs to. -/
structure XR where
  w : WRes
  tok : Bool

/-- `↭`'s `imm` clause at `E = G1 ∨ G2`, with G2 read off the run's start: where the start does
not hold the token, the clause is not read (G2). Where it does, the end→start direction admits
derivable views (G1). -/
def UpdImmE (ρ₁ ρ₂ : XR) : Prop :=
  (∀ (l : Loc) (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join), ρ₁.tok = true →
    ρ₁.w.FlatAt l (CellU.immOf s v χ h) → ρ₂.w.FlatAt l (CellU.immOf s v χ h)) ∧
  (∀ (l : Loc) (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join), ρ₁.tok = true →
    ρ₂.w.FlatAt l (CellU.immOf s v χ h) →
      ρ₁.w.FlatAt l (CellU.immOf s v χ h) ∨
      ∃ σ, ResU.Flat ρ₁.w σ ∧ Derivable σ l (CellU.immOf s v χ h))

theorem updImmE_of_lic {ρ₁ ρ₂ : XR} (h : UpdImmLic ρ₁.w ρ₂.w) : UpdImmE ρ₁ ρ₂ :=
  ⟨fun l s v χ hs _ hf => h.1 l s v χ hs hf, fun l s v χ hs _ hf => h.2 l s v χ hs hf⟩

theorem updImmE_of_noTok {ρ₁ ρ₂ : XR} (h : ρ₁.tok = false) : UpdImmE ρ₁ ρ₂ :=
  ⟨fun _ _ _ _ _ ht => absurd (h.symm.trans ht) Bool.false_ne_true,
    fun _ _ _ _ _ ht => absurd (h.symm.trans ht) Bool.false_ne_true⟩

/-- The `↭` composition bind performs, at `UpdImmE`. -/
def G2Compose : Prop := ∀ ρ₀ ρ₁ ρ₂ : XR, UpdImmE ρ₀ ρ₁ → UpdImmE ρ₁ ρ₂ → UpdImmE ρ₀ ρ₂

/-- **K6: G2 then G1 does not compose.** The chain is:
- `(∅, [α]_1) → (∅, –)`: the token leaves, and `↭` holds unmasked;
- `(∅, –) → (ρ, –)`: G2 conjures the lent cell `0 ↦ imm({α}, loc 1, 1 ↦ own(t))`;
- `(ρ, –) → (π, –)`: G1 derives the getter's image (K1; admitted by its G1 disjunct alone).

The composite starts holding the token, so nothing is exempt. The end's `imm` cell at `0` is
neither in `⦇∅⦈` nor derivable from it. -/
theorem not_g2ThenG1Compose (α : Life) (t : Val) :
    ¬ (∀ ρ₀ ρ₁ ρ₂ ρ₃ : XR, UpdImmE ρ₀ ρ₁ → UpdImmE ρ₁ ρ₂ → UpdImmE ρ₂ ρ₃ → UpdImmE ρ₀ ρ₃) := by
  intro H
  let r₀ : XR := ⟨PMap.empty, true⟩
  let r₁ : XR := ⟨PMap.empty, false⟩
  let r₂ : XR := ⟨rhoK1 α t, false⟩
  let r₃ : XR := ⟨piK1 α t, false⟩
  have h₀₁ : UpdImmE r₀ r₁ := updImmE_of_lic (UpdImmLic.of_updImm fun _ _ _ _ _ => Iff.rfl)
  have h₁₂ : UpdImmE r₁ r₂ := updImmE_of_noTok rfl
  have h₂₃ : UpdImmE r₂ r₃ := updImmE_of_lic (k1_lic α t)
  have h₀₃ := H r₀ r₁ r₂ r₃ h₀₁ h₁₂ h₂₃
  rcases h₀₃.2 0 (LSet.singleton α) (Val.loc 1) (chiK1 t) (chiK1_inStratum _ t) rfl
      ⟨agPi α t, flat_piK1 α t, agPi_get0 α t⟩ with ⟨σ, hσ, e⟩ | ⟨σ, hσ, hd⟩
  · rw [flat_empty_eq hσ, PMap.empty_get] at e
    cases e
  · rw [flat_empty_eq hσ] at hd
    exact not_derivable_empty hd

/-- **K6 in the two-run form bind uses.** -/
theorem not_g2Compose (α : Life) (t : Val) : ¬ G2Compose := by
  intro H
  exact not_g2ThenG1Compose α t fun ρ₀ ρ₁ ρ₂ ρ₃ h₀₁ h₁₂ h₂₃ =>
    H ρ₀ ρ₂ ρ₃ (H ρ₀ ρ₁ ρ₂ h₀₁ h₁₂) h₂₃

end BoCa.Fig16.LicUpd

end
