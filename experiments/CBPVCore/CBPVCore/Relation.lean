import Paper.CONF.Results
import Support.TypedWorld.Compatibility

/-!
# CBPVCore — Relation

Call-by-push-value types over the typed world of `Support/TypedWorld`.

Value types `VTy`: `1`, `⊗`, `0`, `⊕`, `U`, and the resource types `Ref`, `Imm @a`, `Mut @a`,
`[@a]`, `!`, `Unk`.  Computation types `CTy`: `F`, `⊸`, `&`, `⊤`, and the lifetime `∀'x ⊏ @b`.

`vC`/`cC` interpret them over `wpTS`: the Kripke quantifier over `Ext` sits at `U` only, the
tagged `wpTS` at `F` only.  `vC` is mode-indexed like the typed world's `vX`: `false` is the
observable view an `Imm` payload is held at, with `U` relaxed to `True`.  The resource clauses
are `vX`'s (`ptoOwn`, `ptoImmS`, `ptoMutS`, `atLife`/`box`, `ρ = ∅` at `!`, `emp` at `Unk`); the
`Imm` clause's `CohE` is read at a BoLo preimage of the payload under `cbv`.

A thunk of `F A` is `λ_. M`, forced by applying it to `()`; a thunk of any other computation
type is the λ-value that computation is, forced by using it as it stands (`forceE`).

`cC` is written curried on the connective; `cC_iff_stacks` shows it is the stack semantics:
`𝒞⟦C⟧(e) = ∀ S matching C. 𝒮⟦C⟧(S) ─⋆ wpTS (S[e]) (post S)`, where a stack is the list of
values the computation is applied to (an argument for `⊸`, `inj₁ ()` or `inj₂ ()` for a
projection of `&`, `()` for an instance of `∀`), `𝒮⟦C⟧` separates the arguments' relations and
fixes the postcondition at the final `F A`, and `⊤` has no stacks.
-/

namespace CBPVCore
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Typed
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
noncomputable section

mutual
/-- Value types. -/
inductive VTy where
  | unit
  | tensor (A B : VTy)
  | zero
  | sum (A B : VTy)
  /-- `U C`. -/
  | thunk (C : CTy)
  /-- `Ref A`. -/
  | ref (A : VTy)
  /-- `Imm @a A`. -/
  | imm (a : Lifetime.Life) (A : VTy)
  /-- `Mut @a A`. -/
  | mut (a : Lifetime.Life) (A : VTy)
  /-- `[@a] A`. -/
  | box (a : Lifetime.Life) (A : VTy)
  /-- `!A`. -/
  | bang (A : VTy)
  /-- `Unk`. -/
  | unk
/-- Computation types. -/
inductive CTy where
  /-- `F A`. -/
  | ret (A : VTy)
  /-- `A ⊸ C`. -/
  | arr (A : VTy) (C : CTy)
  /-- `C & D`. -/
  | amp (C D : CTy)
  /-- `⊤`. -/
  | top
  /-- `∀'x ⊏ @b. C`. -/
  | all (x : LifeVar) (b : Lifetime.Life) (C : CTy)
end

/-- The call-by-value translation of BoLo types: `T₁ ⊸ T₂ ↦ U (T₁⁺ ⊸ F T₂⁺)`,
`∀'x ⊏ @b. T ↦ U (∀'x ⊏ @b. F T⁺)`, and every other former to its namesake. -/
def cbv : Ty → VTy
  | .unit => .unit
  | .sum T₁ T₂ => .sum (cbv T₁) (cbv T₂)
  | .tensor T₁ T₂ => .tensor (cbv T₁) (cbv T₂)
  | .lolli T₁ T₂ => .thunk (.arr (cbv T₁) (.ret (cbv T₂)))
  | .ref T => .ref (cbv T)
  | .bang T => .bang (cbv T)
  | .imm a T => .imm a (cbv T)
  | .mut a T => .mut a (cbv T)
  | .box a T => .box a (cbv T)
  | .all x b T => .thunk (.all x b (.ret (cbv T)))
  | .unk => .unk

theorem cbv_injective : ∀ {S T : Ty}, cbv S = cbv T → S = T
  | .unit, T, h => by cases T <;> simp_all [cbv]
  | .unk, T, h => by cases T <;> simp_all [cbv]
  | .sum S₁ S₂, T, h => by
      cases T <;> simp [cbv] at h
      exact congrArg₂ _ (cbv_injective h.1) (cbv_injective h.2)
  | .tensor S₁ S₂, T, h => by
      cases T <;> simp [cbv] at h
      exact congrArg₂ _ (cbv_injective h.1) (cbv_injective h.2)
  | .lolli S₁ S₂, T, h => by
      cases T <;> simp [cbv] at h
      exact congrArg₂ _ (cbv_injective h.1) (cbv_injective h.2)
  | .ref S, T, h => by
      cases T <;> simp [cbv] at h
      exact congrArg _ (cbv_injective h)
  | .bang S, T, h => by
      cases T <;> simp [cbv] at h
      exact congrArg _ (cbv_injective h)
  | .imm a S, T, h => by
      cases T <;> simp [cbv] at h
      rw [h.1, cbv_injective h.2]
  | .mut a S, T, h => by
      cases T <;> simp [cbv] at h
      rw [h.1, cbv_injective h.2]
  | .box a S, T, h => by
      cases T <;> simp [cbv] at h
      rw [h.1, cbv_injective h.2]
  | .all x b S, T, h => by
      cases T <;> simp [cbv] at h
      rw [h.1, h.2.1, cbv_injective h.2.2]

/-- `force`, at the computation type forced.  A thunk of `F A` is `λ_. M` and is forced by
applying it to `()`; a thunk of any other computation type is the λ-value that computation
already is, and is forced by using it as it stands. -/
def forceE : CTy → Expr → Expr
  | .ret _, e => .app e (.val .unit)
  | _, e => e

mutual
/-- `𝒱⟦A⟧(ls)δ(v)`.  `full = true`: the program's relation.  `full = false`: the observable
view an `Imm` payload is held at, with `U` positions relaxed to `True` (`vX`'s `false` mode). -/
def vC : Bool → VTy → List SRec → LSub → Val → WProp
  | _, .unit, _, _, v => ⌜v = .unit⌝
  | b, .tensor A B, ls, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vC b A ls δ v₁ ⋆ vC b B ls δ v₂
  | _, .zero, _, _, _ => fun _ => False
  | b, .sum A B, ls, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vC b A ls δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vC b B ls δ v₂)
  | true, .thunk C, ls, δ, v => fun ρ =>
      ∀ ls', Ext ls ls' ρ → cC C ls' δ (forceE C (.val v)) ρ
  | false, .thunk _, _, _, _ => fun _ => True
  | _, .bang A, ls, δ, v => fun ρ => ρ = PMap.empty ∧ vC true A ls δ v ρ
  | b, .box a A, ls, δ, v => atLife δ a fun α => box α (vC b A ls δ v)
  | b, .ref A, ls, δ, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vC b A ls δ v'
  | _, .imm a A, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ =>
        ⌜v = .loc ℓ ∧ ∃ T, cbv T = A ∧ CohE (rsOf ls) ℓ T δ⌝ ⋆
        ptoImmS ℓ α ls (fun ls₀ => vC false A ls₀ δ)
  | _, .mut a A, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
        ptoMutS ℓ α ls (fun ls₀ => vC true A ls₀ δ)
  | _, .unk, _, _, _ => emp
/-- `𝒞⟦C⟧(ls)δ(e)`, curried on the connective. -/
def cC : CTy → List SRec → LSub → Expr → WProp
  | .ret A, ls, δ, e => wpTS ls e (fun ls'' => vC true A ls'' δ)
  | .arr A C, ls, δ, e => fun ρ =>
      ∀ v, (vC true A ls δ v ─⋆ cC C ls δ (.app e (.val v))) ρ
  | .amp C D, ls, δ, e => fun ρ =>
      cC C ls δ (.app e (.val (.inj₁ .unit))) ρ ∧ cC D ls δ (.app e (.val (.inj₂ .unit))) ρ
  | .top, _, _, _ => fun _ => True
  | .all x c C, ls, δ, e => fun ρ =>
      ∀ α, (⌜LtLife δ c α⌝ ─⋆ cC C ls (δ.extend x α) (.app e (.val .unit))) ρ
end

/-! ### Stacks -/

/-- `S[e]`: `e` applied to the stack's values, innermost first. -/
def plugS : List Val → Expr → Expr
  | [], e => e
  | v :: S, e => plugS S (.app e (.val v))

/-- `𝒮⟦C⟧(ls)δ(S, Q)`: `S` is a stack for `C` whose final `F A` has postcondition `Q`, and the
resource holds its arguments. -/
def sS : CTy → List SRec → LSub → List Val → (List SRec → Val → WProp) → WProp
  | .ret A, _, δ, [], Q => ⌜Q = fun ls'' => vC true A ls'' δ⌝
  | .arr A C, ls, δ, v :: S, Q => vC true A ls δ v ⋆ sS C ls δ S Q
  | .amp C D, ls, δ, v :: S, Q =>
      BoLo.or (⌜v = .inj₁ .unit⌝ ⋆ sS C ls δ S Q) (⌜v = .inj₂ .unit⌝ ⋆ sS D ls δ S Q)
  | .all x c C, ls, δ, v :: S, Q =>
      ex fun α => ⌜v = .unit ∧ LtLife δ c α⌝ ⋆ sS C ls (δ.extend x α) S Q
  | _, _, _, _, _ => fun _ => False

/-- `cC` is the stack semantics. -/
theorem cC_iff_stacks : ∀ (C : CTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes),
    cC C ls δ e ρ ↔ ∀ S Q, (sS C ls δ S Q ─⋆ wpTS ls (plugS S e) Q) ρ
  | .ret A, ls, δ, e, ρ => by
      constructor
      · intro hw S Q ρ₁ ρ₂ hs hc
        cases S with
        | nil =>
            obtain ⟨rfl, rfl⟩ := hs
            rw [eq_of_compS_empty_left (ResU.CompS.comm hc)]
            exact hw
        | cons v S => exact hs.elim
      · intro h
        exact h [] _ PMap.empty ρ ⟨rfl, rfl⟩ (ResU.comp_empty_right ρ)
  | .arr A C, ls, δ, e, ρ => by
      constructor
      · intro h S Q ρ₁ ρ₂ hs hc
        cases S with
        | nil => exact hs.elim
        | cons v S =>
            obtain ⟨a, b, hab, ha, hb⟩ := hs
            obtain ⟨x, hx, hxb⟩ := compS_reassoc' hab hc
            exact (cC_iff_stacks C ls δ _ x).mp (h v a x ha hx) S Q b ρ₂ hb hxb
      · intro h v a x ha hx
        refine (cC_iff_stacks C ls δ _ x).mpr ?_
        intro S Q b y hb hy
        obtain ⟨z, hz, hzy⟩ := compS_reassoc hx hy
        exact h (v :: S) Q z y ⟨a, b, hz, ha, hb⟩ hzy
  | .amp C D, ls, δ, e, ρ => by
      constructor
      · rintro ⟨h₁, h₂⟩ S Q ρ₁ ρ₂ hs hc
        cases S with
        | nil => exact hs.elim
        | cons v S =>
            rcases hs with hs | hs
            · obtain ⟨rfl, hs'⟩ := pure_sep_iff.mp hs
              exact (cC_iff_stacks C ls δ _ ρ).mp h₁ S Q ρ₁ ρ₂ hs' hc
            · obtain ⟨rfl, hs'⟩ := pure_sep_iff.mp hs
              exact (cC_iff_stacks D ls δ _ ρ).mp h₂ S Q ρ₁ ρ₂ hs' hc
      · intro h
        refine ⟨(cC_iff_stacks C ls δ _ ρ).mpr ?_, (cC_iff_stacks D ls δ _ ρ).mpr ?_⟩
        · intro S Q ρ₁ ρ₂ hs hc
          exact h (_ :: S) Q ρ₁ ρ₂ (Or.inl (pure_sep_mk rfl hs)) hc
        · intro S Q ρ₁ ρ₂ hs hc
          exact h (_ :: S) Q ρ₁ ρ₂ (Or.inr (pure_sep_mk rfl hs)) hc
  | .top, ls, δ, e, ρ => by
      constructor
      · intro _ S Q ρ₁ ρ₂ hs _
        cases S <;> exact hs.elim
      · intro _; trivial
  | .all x c C, ls, δ, e, ρ => by
      constructor
      · intro h S Q ρ₁ ρ₂ hs hc
        cases S with
        | nil => exact hs.elim
        | cons v S =>
            obtain ⟨α, hs⟩ := hs
            obtain ⟨⟨rfl, hlt⟩, hs'⟩ := pure_sep_iff.mp hs
            exact (cC_iff_stacks C ls (δ.extend x α) _ ρ).mp
              (h α PMap.empty ρ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ)) S Q ρ₁ ρ₂ hs' hc
      · intro h α a y ha hy
        obtain ⟨rfl, hlt⟩ := ha
        rw [eq_of_compS_empty_left (ResU.CompS.comm hy)]
        refine (cC_iff_stacks C ls (δ.extend x α) _ ρ).mpr ?_
        intro S Q ρ₁ ρ₂ hs hc
        exact h (.unit :: S) Q ρ₁ ρ₂ ⟨α, pure_sep_mk ⟨rfl, hlt⟩ hs⟩ hc

/-! ### Stability of `𝒱⟦A⟧` along the list -/

/-- `𝒱⟦A⟧` is stable along `Ext` at every value type, in both modes: the Kripke quantifier
sits at `U`, and a cell reads the list only through the records it keeps (`vX_local`). -/
theorem vC_local : ∀ (b : Bool) (A : VTy) {ls ls' : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    Ext ls ls' ρ → vC b A ls δ v ρ → vC b A ls' δ v ρ
  | _, .unit, _, _, _, _, _, _, h => h
  | b, .tensor A B, _, _, _, _, _, hk, h => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      have hk' := hk.right hc
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc',
        vC_local b A (hk'.left hc') h₁, vC_local b B (hk'.right hc') h₂⟩
  | _, .zero, _, _, _, _, _, _, h => h
  | b, .sum A B, _, _, _, _, _, hk, h => by
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, vC_local b A (hk.right hc) h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, vC_local b B (hk.right hc) h₂⟩
  | true, .thunk _, _, _, _, _, _, hk, h => fun ls'' hk' => h ls'' (hk.trans hk')
  | false, .thunk _, _, _, _, _, _, _, h => h
  | _, .bang A, _, _, _, _, _, hk, h => ⟨h.1, vC_local true A hk h.2⟩
  | b, .box a A, _, _, _, _, _, hk, h => by
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, vC_local b A hk hb, ho⟩
  | b, .ref A, _, _, _, _, _, hk, h => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho,
        vC_local b A ((hk.right hc).right hc') h₂⟩
  | _, .imm a A, ls, ls', _, _, _, hk, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, T₀, hT₀, hcoh⟩, s, u, σ, hs, ls₀, hρ₁, hP, hαs,
        hls₀⟩ := h
      subst hρ₀
      have hρ₁' := eq_of_compS_empty_left hc
      subst hρ₁'
      subst hρ₁
      have hk₁ : Keeps (rsOf _) (rsOf _) _ := hk.1
      have hcell : CellIn (ResU.single ℓ (CellU.immOf s u σ hs)) s.meet :=
        CellIn.single (by simp)
      refine ⟨α, hα, ℓ, _, _, hc,
        ⟨rfl, hv, T₀, hT₀, cohE_keeps hk₁ (CellU.kind_immOf _ _ _ _) hcoh⟩,
        s, u, σ, hs, ls₀, rfl, hP, hαs, fun x => ?_⟩
      rw [hls₀ x]
      exact ⟨fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mp hx, hb⟩,
             fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mpr hx, hb⟩⟩
  | _, .mut a A, ls, ls', _, _, _, hk, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, hls₀,
        hunif⟩ := h
      subst hρ₀
      have hk₁ := hk.right hc
      have hmut : CellIn ρ₁ b :=
        ⟨ℓ, _, by rw [hρ₁]; exact ResU.single_get_self _ _, by simp, le_rfl⟩
      refine ⟨α, hα, ℓ, _, _, hc, ⟨rfl, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, ?_, hunif⟩
      intro x
      rw [hls₀ x]
      exact ⟨fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mp hx, hb⟩,
             fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mpr hx, hb⟩⟩
  | _, .unk, _, _, _, _, _, _, h => h

/-- `𝒱⟦A⟧` is carried to a list with the same members (`vP_same` for `vC`). -/
theorem vC_same {b : Bool} {A : VTy} {ls ls' : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : ∀ x, x ∈ ls' ↔ x ∈ ls) (hv : vC b A ls δ v ρ) : vC b A ls' δ v ρ :=
  vC_local b A (ext_of_same h ρ) hv

/-! ### Reduction in front of `wpTS` and `𝒞⟦C⟧` -/

/-- One pure step, in any evaluation context, in front of a `wpTS` (`wpTS_head`, with the step
taken by `Step1`). -/
theorem wpTS_step {e e' : Expr} (h : ∀ μ : Heap, Step1 μ e μ e') (ls : List SRec)
    (Q : List SRec → Val → WProp) : Entails (wpTS ls e' Q) (wpTS ls e Q) := by
  intro ρ hw ρf fρ ps hf hc hT htg
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉, hA, hB,
    hT', htg', hps, hls, hC⟩ := hw ρf fρ ps hf hc hT htg
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇,
    .more (h μ) h₈, h₉, hA, hB, hT', htg', hps, hls, hC⟩

/-- `𝒞⟦C⟧` is closed under a pure step in front. -/
theorem cC_step : ∀ (C : CTy) {e e' : Expr}, (∀ μ : Heap, Step1 μ e μ e') →
    ∀ (ls : List SRec) (δ : LSub), Entails (cC C ls δ e') (cC C ls δ e)
  | .ret _, _, _, h, ls, _ => wpTS_step h ls _
  | .arr _ C, _, _, h, ls, δ => fun _ h' v ρ₁ ρ₂ hv hc =>
      cC_step C (fun μ => (h μ).plug (Kont.appL .hole v)) ls δ _ (h' v ρ₁ ρ₂ hv hc)
  | .amp C D, _, _, h, ls, δ => fun _ ⟨h₁, h₂⟩ =>
      ⟨cC_step C (fun μ => (h μ).plug (Kont.appL .hole _)) ls δ _ h₁,
       cC_step D (fun μ => (h μ).plug (Kont.appL .hole _)) ls δ _ h₂⟩
  | .top, _, _, _, _, _ => fun _ _ => trivial
  | .all x _ C, _, _, h, ls, δ => fun _ h' α ρ₁ ρ₂ hp hc =>
      cC_step C (fun μ => (h μ).plug (Kont.appL .hole _)) ls (δ.extend x α) _
        (h' α ρ₁ ρ₂ hp hc)

/-- One head step in front of `𝒞⟦C⟧`. -/
theorem cC_head (C : CTy) {e e' : Expr} (h : ∀ μ : Heap, Head μ e μ e')
    (ls : List SRec) (δ : LSub) : Entails (cC C ls δ e') (cC C ls δ e) :=
  cC_step C (fun μ => Step1.head (h μ)) ls δ

/-- **Bind at `𝒞⟦C⟧`.**  Run `M` in the hole of `K`, framing `R` through the run; the rest of
the computation — `K` and the stack `C` is eliminated by — continues at the list `M` returns.
`wpTS_bind_frame` at every computation type: the stack's arguments join the frame. -/
theorem cC_bind : ∀ (C : CTy) (K : Kont) (M : Expr) (ls : List SRec) (δ : LSub)
    (P : List SRec → Val → WProp) (R : List SRec → WProp),
    (∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (R ls) (R ls')) →
    (∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ v,
      Entails (P ls' v ⋆ R ls') (cC C ls' δ (K.plug (.val v)))) →
    Entails (wpTS ls M P ⋆ R ls) (cC C ls δ (K.plug M))
  | .ret A, K, M, ls, δ, P, R, hR, h =>
      wpTS_bind_frame K M ls P R (fun ls'' => vC true A ls'' δ) hR h
  | .arr A C, K, M, ls, δ, P, R, hR, h => by
      rintro ρ ⟨ρ₁, ρ₂, hc, hw, hr⟩ v a x ha hx
      obtain ⟨y, hy, hyx⟩ := compS_reassoc hc hx
      refine cC_bind C (.appL K v) M ls δ P (fun l => R l ⋆ vC true A l δ v) ?_ ?_ x
        ⟨ρ₁, y, hyx, hw, ρ₂, a, hy, hr, ha⟩
      · rintro ls' hls σ ⟨σ₁, σ₂, hcσ, h₁, h₂⟩
        exact ⟨σ₁, σ₂, hcσ, hR ls' hls σ₁ h₁, vC_same hls h₂⟩
      · rintro ls' hls w σ ⟨σ₁, σ₂, hcσ, hp, τ₁, τ₂, hcτ, hr', hv⟩
        obtain ⟨z, hz, hzσ⟩ := compS_reassoc' hcτ hcσ
        exact h ls' hls w z ⟨σ₁, τ₁, hz, hp, hr'⟩ v τ₂ σ hv hzσ
  | .amp C D, K, M, ls, δ, P, R, hR, h => fun ρ hρ =>
      ⟨cC_bind C (.appL K _) M ls δ P R hR (fun ls' hls w σ hσ => (h ls' hls w σ hσ).1) ρ hρ,
       cC_bind D (.appL K _) M ls δ P R hR (fun ls' hls w σ hσ => (h ls' hls w σ hσ).2) ρ hρ⟩
  | .top, _, _, _, _, _, _, _, _ => fun _ _ => trivial
  | .all x c C, K, M, ls, δ, P, R, hR, h => by
      rintro ρ hρ α a y ⟨rfl, hlt⟩ hy
      rw [eq_of_compS_empty_left (ResU.CompS.comm hy)]
      exact cC_bind C (.appL K .unit) M ls (δ.extend x α) P R hR
        (fun ls' hls w σ hσ => h ls' hls w σ hσ α PMap.empty σ ⟨rfl, hlt⟩
          (ResU.comp_empty_right σ)) ρ hρ

/-! ### Contexts and the judgment -/

/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧(ls)δ(γ(x))`. -/
def gSepC (ls : List SRec) (δ : LSub) : Ctx VTy → List Val → WProp
  | [],     _      => emp
  | _ :: _, []     => emp
  | s :: Γ, v :: γ => if s.live then vC true s.ty ls δ v ⋆ gSepC ls δ Γ γ else gSepC ls δ Γ γ

/-- `𝒢⟦Γ⟧(ls)δ(γ)`. -/
def gDenC (ls : List SRec) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepC ls δ Γ γ

/-- `Δ; Γ ⊨ e : C`. -/
def SemC (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) : Prop :=
  ∀ δ γ (ls : List SRec) ρ, Δ.Models δ → gDenC ls δ Γ γ ρ → cC C ls δ (substAll γ e) ρ

/-- `Δ; Γ ⊨ V : A` for a value: `return V` at `F A`. -/
abbrev SemV (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy) : Prop := SemC Δ Γ e (.ret A)

theorem gSepC_local {ls ls' : List SRec} {δ : LSub} :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}, Ext ls ls' ρ →
      gSepC ls δ Γ γ ρ → gSepC ls' δ Γ γ ρ
  | [], _, _, _, h => h
  | _ :: _, [], _, _, h => h
  | s :: Γ, v :: γ, ρ, hk, h => by
      unfold gSepC at h ⊢
      split
      · rename_i hl
        rw [if_pos hl] at h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact ⟨ρ₁, ρ₂, hc, vC_local true s.ty (hk.left hc) h₁, gSepC_local (hk.right hc) h₂⟩
      · rename_i hl
        rw [if_neg hl] at h
        exact gSepC_local hk h

theorem gDenC_local {ls ls' : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val}
    {ρ : WRes} (hk : Ext ls ls' ρ) (h : gDenC ls δ Γ γ ρ) : gDenC ls' δ Γ γ ρ := by
  obtain ⟨ρ₁, ρ₂, hc, hp, h₂⟩ := h
  exact ⟨ρ₁, ρ₂, hc, hp, gSepC_local (hk.right hc) h₂⟩

theorem gDenC_iff {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes} :
    gDenC ls δ Γ γ ρ ↔ (Ctx.LiveWithin Γ γ ∧ gSepC ls δ Γ γ ρ) := pure_sep_iff

theorem gDenC_mk {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (hlen : Ctx.LiveWithin Γ γ) (hg : gSepC ls δ Γ γ ρ) : gDenC ls δ Γ γ ρ :=
  gDenC_iff.mpr ⟨hlen, hg⟩

theorem gDenC_same {ls ls' : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (h : ∀ x, x ∈ ls' ↔ x ∈ ls) (hg : gDenC ls δ Γ γ ρ) : gDenC ls' δ Γ γ ρ :=
  gDenC_local (ext_of_same h ρ) hg

theorem gSepC_dead {ls : List SRec} {δ : LSub} : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ →
    ∀ {γ : List Val} {ρ : WRes}, gSepC ls δ Γ γ ρ → ρ = PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ h; exact h.1
  | cons _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' => exact ih (γ := γ') h

theorem gSepC_solo {ls : List SRec} {δ : LSub} : ∀ {Γ : Ctx VTy} {i : Nat} {A : VTy},
    Ctx.Solo Γ i A → ∀ {γ : List Val} {ρ : WRes}, i < γ.length → gSepC ls δ Γ γ ρ →
      ∃ v, γ[i]? = some v ∧ vC true A ls δ v ρ := by
  intro Γ i A hs
  induction hs with
  | @here A Γ' hdead =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
          rw [gSepC_dead hdead hrest] at hc
          rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
          exact ⟨v, rfl, hv⟩
  | @there S A Γ' i' _ ih =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨w, hw, hv⟩ := ih (γ := γ') (by simpa using hlen) hg
          exact ⟨w, by simpa using hw, hv⟩

theorem gSepC_split {ls : List SRec} {δ : LSub} : ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.Split Γ Γ₁ Γ₂ →
    ∀ {γ : List Val} {ρ : WRes}, gSepC ls δ Γ γ ρ →
      (gSepC ls δ Γ₁ γ ⋆ gSepC ls δ Γ₂ γ) ρ := by
  intro Γ Γ₁ Γ₂ hsp
  induction hsp with
  | nil =>
      intro γ ρ h
      refine ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ?_⟩
      cases γ <;> exact ⟨rfl, trivial⟩
  | @left Γ' Γ₁' Γ₂' T _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_reassoc' hcσ hc
          exact ⟨x, σ₂, hxρ, ⟨ρ₁, σ₁, hx, hv, h₁⟩, h₂⟩
  | @right Γ' Γ₁' Γ₂' T _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_lcomm hcσ hc
          exact ⟨σ₁, x, hxρ, h₁, ⟨ρ₁, σ₂, hx, hv, h₂⟩⟩
  | @dead Γ' Γ₁' Γ₂' T _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' => exact ih (γ := γ') h

theorem gDenC_split {ls : List SRec} {δ : LSub} {Γ Γ₁ Γ₂ : Ctx VTy} (hsp : Ctx.Split Γ Γ₁ Γ₂)
    {γ : List Val} {ρ : WRes} (hg : gDenC ls δ Γ γ ρ) :
    (gDenC ls δ Γ₁ γ ⋆ gDenC ls δ Γ₂ γ) ρ := by
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp hg
  obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := gSepC_split hsp hs
  exact ⟨ρ₁, ρ₂, hc, gDenC_mk (hsp.liveWithin hlen).1 h₁, gDenC_mk (hsp.liveWithin hlen).2 h₂⟩

/-- A dead slot contributes nothing. -/
theorem gDenC_dead_cons {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (A : VTy) (v : Val) (hg : gDenC ls δ Γ γ ρ) : gDenC ls δ (⟨A, false⟩ :: Γ) (v :: γ) ρ := by
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp hg
  exact gDenC_mk (by simpa using hlen) (by simpa [gSepC] using hs)

/-! ### Lifetime variables -/

mutual
/-- `'x` occurs free in `A`; `∀'y ⊏ @b. C` binds `'y` in `C` and not in `@b` (`LFree`). -/
def VFree (x : LifeVar) : VTy → Prop
  | .unit => False
  | .zero => False
  | .unk => False
  | .tensor A B => VFree x A ∨ VFree x B
  | .sum A B => VFree x A ∨ VFree x B
  | .thunk C => CFree x C
  | .ref A => VFree x A
  | .bang A => VFree x A
  | .imm a A => a.mentions x = true ∨ VFree x A
  | .mut a A => a.mentions x = true ∨ VFree x A
  | .box a A => a.mentions x = true ∨ VFree x A
/-- `'x` occurs free in `C`. -/
def CFree (x : LifeVar) : CTy → Prop
  | .ret A => VFree x A
  | .arr A C => VFree x A ∨ CFree x C
  | .amp C D => CFree x C ∨ CFree x D
  | .top => False
  | .all y b C => b.mentions x = true ∨ (x ≠ y ∧ CFree x C)
end

/-- The translation keeps the free lifetime variables. -/
theorem lFree_iff_vFree (x : LifeVar) : ∀ T : Ty, LFree x T ↔ VFree x (cbv T)
  | .unit => Iff.rfl
  | .unk => Iff.rfl
  | .sum A B => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A, lFree_iff_vFree x B]
  | .tensor A B => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A, lFree_iff_vFree x B]
  | .lolli A B => by
      simp only [LFree, VFree, CFree, cbv, lFree_iff_vFree x A, lFree_iff_vFree x B]
  | .ref A => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A]
  | .bang A => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A]
  | .imm a A => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A]
  | .mut a A => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A]
  | .box a A => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A]
  | .all y b A => by simp only [LFree, VFree, CFree, cbv, lFree_iff_vFree x A]

mutual
/-- `𝒱⟦A⟧δ` reads `δ` only at the variables free in `A` (`vX_congr`). -/
theorem vC_congr : ∀ (A : VTy) {δ₁ δ₂ : LSub}, (∀ y, VFree y A → δ₁.find? y = δ₂.find? y) →
    ∀ (b : Bool) (ls : List SRec), vC b A ls δ₁ = vC b A ls δ₂
  | .unit, _, _, _, b, _ => by cases b <;> rfl
  | .zero, _, _, _, b, _ => by cases b <;> rfl
  | .unk, _, _, _, b, _ => by cases b <;> rfl
  | .tensor A B, _, _, h, b, ls => by
      have h₁ := vC_congr A (fun y hy => h y (Or.inl hy))
      have h₂ := vC_congr B (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vC, h₁, h₂]
  | .sum A B, _, _, h, b, ls => by
      have h₁ := vC_congr A (fun y hy => h y (Or.inl hy))
      have h₂ := vC_congr B (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vC, h₁, h₂]
  | .thunk C, _, _, h, b, ls => by
      have hC := cC_congr C h
      funext v; cases b
      · rfl
      · simp only [vC, hC]
  | .ref A, _, _, h, b, ls => by
      have ih := vC_congr A h
      funext v; cases b <;> simp only [vC, ih]
  | .bang A, _, _, h, b, ls => by
      have ih := vC_congr A h
      funext v; cases b <;> simp only [vC, ih]
  | .box a A, δ₁, δ₂, h, b, ls => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vC_congr A (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vC, ih, atLife_congr' ha]
  | .imm a A, δ₁, δ₂, h, b, ls => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vC_congr A (fun y hy => h y (Or.inr hy))
      have hcoh : ∀ rs m, (∃ T, cbv T = A ∧ CohE rs m T δ₁) = (∃ T, cbv T = A ∧ CohE rs m T δ₂) :=
        fun rs m => propext
          ⟨fun ⟨T, hT, hc⟩ => ⟨T, hT, hc.tyEq (TyEq.of_agree T (fun y hy =>
              (h y (Or.inr (hT ▸ (lFree_iff_vFree y T).mp hy))).symm))⟩,
           fun ⟨T, hT, hc⟩ => ⟨T, hT, hc.tyEq (TyEq.of_agree T (fun y hy =>
              h y (Or.inr (hT ▸ (lFree_iff_vFree y T).mp hy))))⟩⟩
      funext v; cases b <;> simp only [vC, ih, hcoh, atLife_congr' ha]
  | .mut a A, δ₁, δ₂, h, b, ls => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vC_congr A (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vC, ih, atLife_congr' ha]
/-- `𝒞⟦C⟧δ` reads `δ` only at the variables free in `C`. -/
theorem cC_congr : ∀ (C : CTy) {δ₁ δ₂ : LSub}, (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) →
    ∀ (ls : List SRec), cC C ls δ₁ = cC C ls δ₂
  | .ret A, _, _, h, ls => by
      have ih := vC_congr A h true
      funext e; simp only [cC, ih]
  | .arr A C, _, _, h, ls => by
      have h₁ := vC_congr A (fun y hy => h y (Or.inl hy)) true ls
      have h₂ := cC_congr C (fun y hy => h y (Or.inr hy)) ls
      funext e; simp only [cC, h₁, h₂]
  | .amp C D, _, _, h, ls => by
      have h₁ := cC_congr C (fun y hy => h y (Or.inl hy)) ls
      have h₂ := cC_congr D (fun y hy => h y (Or.inr hy)) ls
      funext e; simp only [cC, h₁, h₂]
  | .top, _, _, _, _ => rfl
  | .all x c C, δ₁, δ₂, h, ls => by
      have hc : c.interp δ₁ = c.interp δ₂ := interp_congr c (fun y hy => h y (Or.inl hy))
      have hC : ∀ α : Life, cC C ls (δ₁.extend x α) = cC C ls (δ₂.extend x α) := by
        intro α
        refine cC_congr C (fun y hy => ?_) ls
        by_cases hxy : x = y
        · subst hxy; rw [find?_extend_self, find?_extend_self]
        · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
          exact h y (Or.inr ⟨Ne.symm hxy, hy⟩)
      have hL : ∀ α : Life, LtLife δ₁ c α = LtLife δ₂ c α := by intro α; unfold LtLife; rw [hc]
      funext e; simp only [cC, hC, hL]
end

theorem vC_extend_of_not_free {x : LifeVar} {A : VTy} (h : ¬ VFree x A) (b : Bool)
    (ls : List SRec) (δ : LSub) (α : Life) : vC b A ls (δ.extend x α) = vC b A ls δ :=
  vC_congr A (fun y hy => find?_extend_ne δ α (fun e => by subst e; exact h hy)) b ls

theorem gSepC_congr {ls : List SRec} {δ₁ δ₂ : LSub} : ∀ {Γ : Ctx VTy} {γ : List Val},
    (∀ s ∈ Γ, s.live = true → vC true s.ty ls δ₁ = vC true s.ty ls δ₂) →
    gSepC ls δ₁ Γ γ = gSepC ls δ₂ Γ γ := by
  intro Γ
  induction Γ with
  | nil => intro γ _; cases γ <;> rfl
  | cons s Γ' ih =>
      intro γ h
      cases γ with
      | nil => rfl
      | cons v γ' =>
          have htail : ∀ t ∈ Γ', t.live = true → vC true t.ty ls δ₁ = vC true t.ty ls δ₂ :=
            fun t ht => h t (List.mem_cons_of_mem _ ht)
          by_cases hl : s.live
          · simp only [gSepC, if_pos hl, ih htail, h s (List.mem_cons_self ..) hl]
          · simp only [gSepC, if_neg hl, ih htail]

/-- `!Γ`: every live slot is at a `!` type. -/
def Persistent (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → ∃ A, s.ty = .bang A

/-- `!Γ` holds no resource (`gSepX_persistent`). -/
theorem gSepC_persistent {ls : List SRec} {δ : LSub} :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}, Persistent Γ → gSepC ls δ Γ γ ρ → ρ = PMap.empty
  | [], _, _, _, h => h.1
  | _ :: _, [], _, _, h => h.1
  | s :: Γ, v :: γ, ρ, hp, h => by
      have hp' : Persistent Γ := fun t ht hl => hp t (List.mem_cons_of_mem _ ht) hl
      unfold gSepC at h
      split at h
      · rename_i hl
        obtain ⟨A, hA⟩ := hp s List.mem_cons_self hl
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        have e₁ : ρ₁ = PMap.empty := by rw [hA] at h₁; exact h₁.1
        have e₂ := gSepC_persistent hp' h₂
        subst e₁; subst e₂
        exact eq_of_compS_empty_left hc
      · exact gSepC_persistent hp' h

/-- A consumed context denotes `emp`, whatever its slots' types. -/
theorem gDenC_dead_eq {ls : List SRec} {δ : LSub} {Γ₁ Γ₂ : Ctx VTy} (h₁ : Ctx.Dead Γ₁)
    (h₂ : Ctx.Dead Γ₂) (γ : List Val) : gDenC ls δ Γ₁ γ = gDenC ls δ Γ₂ γ := by
  have hs : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → ∀ γ, gSepC ls δ Γ γ = emp := by
    intro Γ hd
    induction hd with
    | nil => intro γ; cases γ <;> rfl
    | cons _ ih => intro γ; cases γ with
      | nil => rfl
      | cons v γ => simp only [gSepC, Bool.false_eq_true, if_false, ih]
  have hl : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → ∀ γ : List Val, Ctx.LiveWithin Γ γ := by
    intro Γ hd
    induction hd with
    | nil => intro γ; simp
    | cons _ ih => intro γ; cases γ with
      | nil => exact ⟨by simp, ih []⟩
      | cons v γ => exact ih γ
  unfold gDenC
  rw [hs h₁, hs h₂, propext (iff_of_true (hl h₁ γ) (hl h₂ γ))]

/-- `SemC` at a consumed context does not read the slots' types. -/
theorem semC_dead {Δ : LifeCtx} {Γ₁ Γ₂ : Ctx VTy} {e : Expr} {C : CTy} (h₁ : Ctx.Dead Γ₁)
    (h₂ : Ctx.Dead Γ₂) (h : SemC Δ Γ₁ e C) : SemC Δ Γ₂ e C := by
  intro δ γ ls ρ hδ hg
  rw [gDenC_dead_eq h₂ h₁] at hg
  exact h δ γ ls ρ hδ hg

/-- `Γ₁` and `Γ₂` have the same live slots, at the same positions and types; their dead slots
may be at different types. -/
inductive LiveEq : Ctx VTy → Ctx VTy → Prop where
  | nil : LiveEq [] []
  | live {A : VTy} {Γ₁ Γ₂ : Ctx VTy} : LiveEq Γ₁ Γ₂ → LiveEq (⟨A, true⟩ :: Γ₁) (⟨A, true⟩ :: Γ₂)
  | dead {A B : VTy} {Γ₁ Γ₂ : Ctx VTy} : LiveEq Γ₁ Γ₂ →
      LiveEq (⟨A, false⟩ :: Γ₁) (⟨B, false⟩ :: Γ₂)

theorem gSepC_liveEq {ls : List SRec} {δ : LSub} {Γ₁ Γ₂ : Ctx VTy} (h : LiveEq Γ₁ Γ₂) :
    ∀ γ, gSepC ls δ Γ₁ γ = gSepC ls δ Γ₂ γ := by
  induction h with
  | nil => intro γ; cases γ <;> rfl
  | live _ ih => intro γ; cases γ with
    | nil => rfl
    | cons v γ => simp only [gSepC, if_true, ih]
  | dead _ ih => intro γ; cases γ with
    | nil => rfl
    | cons v γ => simp only [gSepC, Bool.false_eq_true, if_false, ih]

theorem liveWithin_liveEq {Γ₁ Γ₂ : Ctx VTy} (h : LiveEq Γ₁ Γ₂) :
    ∀ γ : List Val, Ctx.LiveWithin Γ₁ γ ↔ Ctx.LiveWithin Γ₂ γ := by
  induction h with
  | nil => intro γ; simp
  | live _ ih => intro γ; cases γ with
    | nil => simp only [Ctx.liveWithin_cons_nil]; simp
    | cons v γ => simp only [Ctx.liveWithin_cons]; exact ih γ
  | dead _ ih => intro γ; cases γ with
    | nil => simp only [Ctx.liveWithin_cons_nil]; exact and_congr Iff.rfl (ih [])
    | cons v γ => simp only [Ctx.liveWithin_cons]; exact ih γ

/-- The context relation does not read the types of dead slots. -/
theorem gDenC_liveEq {ls : List SRec} {δ : LSub} {Γ₁ Γ₂ : Ctx VTy} (h : LiveEq Γ₁ Γ₂)
    (γ : List Val) : gDenC ls δ Γ₁ γ = gDenC ls δ Γ₂ γ := by
  unfold gDenC
  rw [gSepC_liveEq h γ, propext (liveWithin_liveEq h γ)]

theorem semC_liveEq {Δ : LifeCtx} {Γ₁ Γ₂ : Ctx VTy} {e : Expr} {C : CTy} (hE : LiveEq Γ₁ Γ₂) :
    SemC Δ Γ₁ e C ↔ SemC Δ Γ₂ e C := by
  simp only [SemC, gDenC_liveEq hE]

end
end CBPVCore
