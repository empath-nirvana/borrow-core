import Recursion.Fix
import Paper.Examples.Programs

/-!
# Recursion — P-μ: the boxed list as a least fixed point

`L = μX. 1 ⊕ Ref X`, written out by hand over CBPVWorld's relation, which is imported unchanged.
`listF P` is `vC`'s `⊕`, `1` and `Ref` clauses with the candidate `P` in place of `vC b X`
(`listF_vC`: at `P = vC · A` it is `vC` at `1 ⊕ Ref A`). `listRel` is Knaster–Tarski's least
fixed point `⋂{P | listF P ⊆ P}`, written in `Prop`: its definition needs no monotonicity; the
unrolling does (`listF_mono`).

* `listRel_unroll`: `listRel ↔ listF listRel`.
* `listRel_outlives`: `[TR]` 6.60's shape, at every lifetime (the list holds `own` cells only).
* `listRel_local`: `Ext`-stability, `vC_local`'s shape.
* `freeAll`: the Z-combinator term that frees every cell; `freeAll_sem` is its semantic type
  `U(L ⊸ F 1)`, by induction on the least fixed point.
* `build3Free_runs`: a 3-cell list built by a `CDerives` derivation at the finite unrolling
  `approx 3`, then freed; it runs from the empty memory to `()` and the empty memory.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVWorld.Recursion
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A candidate interpretation of a value-type variable, at `vC`'s signature: mode, record list,
lifetime substitution, value. -/
abbrev VPred := Bool → List SRec → LSub → Val → WProp

/-- `P ⊆ Q` pointwise. -/
def VPred.Le (P Q : VPred) : Prop := ∀ b ls δ v, Entails (P b ls δ v) (Q b ls δ v)

/-! ### The functor and its least fixed point -/

/-- One unfolding of `L = μX. 1 ⊕ Ref X` at the candidate `P` for `X`: `vC`'s `⊕`, `1` and `Ref`
clauses with `P b` in place of `vC b X`. -/
def listF (P : VPred) : VPred := fun b ls δ v =>
  BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ ⌜v₁ = .unit⌝)
    (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆
      ex fun ℓ => ex fun v' => ⌜v₂ = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ P b ls δ v')

/-- `listF` transcribes `vC`: at `P = vC · A` it is `vC` at `1 ⊕ Ref A`. -/
theorem listF_vC (A : VTy) (b : Bool) (ls : List SRec) (δ : LSub) (v : Val) :
    listF (fun b => vC b A) b ls δ v = vC b (.sum .unit (.ref A)) ls δ v := by
  cases b <;> simp only [listF, vC]

theorem listF_mono {P Q : VPred} (h : P.Le Q) : (listF P).Le (listF Q) := by
  rintro b ls δ v ρ (h₁ | ⟨v₂, ρ₀, ρ₃, hc, hp, ℓ, v', ρa, ρb, hc', hpl, ρ₁, ρ₂, hc'', ho, hP⟩)
  · exact Or.inl h₁
  · exact Or.inr ⟨v₂, ρ₀, ρ₃, hc, hp, ℓ, v', ρa, ρb, hc', hpl, ρ₁, ρ₂, hc'', ho,
      h b ls δ v' ρ₂ hP⟩

/-- `P` is closed under one unfolding. -/
def Prefixed (P : VPred) : Prop := (listF P).Le P

/-- `⟦μX. 1 ⊕ Ref X⟧ = ⋂{P | listF P ⊆ P}`. -/
def listRel : VPred := fun b ls δ v ρ => ∀ P : VPred, Prefixed P → P b ls δ v ρ

/-- Induction on the least fixed point. -/
theorem listRel_ind {P : VPred} (hP : Prefixed P) : listRel.Le P :=
  fun _ _ _ _ _ h => h P hP

/-- `roll`. -/
theorem listRel_roll : Prefixed listRel :=
  fun b ls δ v ρ h _ hP => hP b ls δ v ρ (listF_mono (listRel_ind hP) b ls δ v ρ h)

/-- `unroll`. -/
theorem listRel_unfold : listRel.Le (listF listRel) :=
  listRel_ind (P := listF listRel) (listF_mono listRel_roll)

/-- **The unroll equation.** -/
theorem listRel_unroll (b : Bool) (ls : List SRec) (δ : LSub) (v : Val) (ρ : WRes) :
    listRel b ls δ v ρ ↔ listF listRel b ls δ v ρ :=
  ⟨listRel_unfold b ls δ v ρ, listRel_roll b ls δ v ρ⟩

/-! ### 6.60's shape and `Ext`-stability -/

/-- `[TR]` 6.60's shape at `L`: a list outlives every lifetime. `L[1/X] = 1 ⊕ Ref 1`
outlives every lifetime, and the induction on the least fixed point carries that to `L`. -/
theorem listRel_outlives (α : Life) {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : listRel b ls δ v ρ) : BoLo.Outlives ρ α := by
  refine listRel_ind (P := fun _ _ _ _ ρ => BoLo.Outlives ρ α) ?_ b ls δ v ρ h
  rintro b ls δ v ρ (⟨v₁, hs⟩ | ⟨v₂, hs⟩)
  · obtain ⟨-, rfl, -⟩ := pure_sep_iff.mp hs
    exact ResU.inStratum_empty α
  · obtain ⟨-, ℓ, v', hs'⟩ := pure_sep_iff.mp hs
    obtain ⟨-, ρ₁, ρ₂, hc, rfl, h₂⟩ := pure_sep_iff.mp hs'
    exact (outlives_comp hc α).mpr ⟨ResU.inStratum_single_own α ℓ v', h₂⟩

/-- `Ext`-stability (`vC_local`'s shape), by induction on the least fixed point. -/
theorem listRel_local {b : Bool} {ls ls' : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (hk : Ext ls ls' ρ) (h : listRel b ls δ v ρ) : listRel b ls' δ v ρ := by
  refine listRel_ind (P := fun b ls δ v ρ => ∀ ls', Ext ls ls' ρ → listRel b ls' δ v ρ) ?_
    b ls δ v ρ h ls' hk
  rintro b ls δ v ρ (h₁ | ⟨v₂, ρ₀, ρ₃, hc, hp, ℓ, v', ρa, ρb, hc', hpl, ρ₁, ρ₂, hc'', ho, hP⟩)
    ls' hk
  · exact listRel_roll b ls' δ v ρ (Or.inl h₁)
  · exact listRel_roll b ls' δ v ρ (Or.inr ⟨v₂, ρ₀, ρ₃, hc, hp, ℓ, v', ρa, ρb, hc', hpl, ρ₁, ρ₂,
      hc'', ho, hP ls' (((hk.right hc).right hc').right hc'')⟩)

/-! ### The finite unrollings are value types -/

/-- `approx n`: `L` unrolled `n + 1` times, closed with `0`. A list of at most `n` cells. -/
def approx : Nat → VTy
  | 0 => .sum .unit (.ref .zero)
  | n + 1 => .sum .unit (.ref (approx n))

/-- Every finite unrolling is contained in `L`. -/
theorem listRel_of_approx : ∀ (n : Nat) {b : Bool} {ls : List SRec} {δ : LSub} {v : Val}
    {ρ : WRes}, vC b (approx n) ls δ v ρ → listRel b ls δ v ρ
  | 0, b, ls, δ, v, ρ, h => by
      rw [approx, ← listF_vC] at h
      refine listRel_roll b ls δ v ρ (listF_mono ?_ b ls δ v ρ h)
      intro b _ _ _ _ h'
      cases b <;> exact h'.elim
  | n + 1, b, ls, δ, v, ρ, h => by
      rw [approx, ← listF_vC] at h
      exact listRel_roll b ls δ v ρ
        (listF_mono (fun _ _ _ _ _ h' => listRel_of_approx n h') b ls δ v ρ h)

/-! ### `freeAll` -/

/-- The body of `freeAll = Z (λself. λl. case l {inj₁ u. u | inj₂ r. self (free r)})`. -/
def faB : Expr := .case (.var 0) (.var 0) (.app (.var 2) (.app (.val (.prim .free)) (.var 0)))

theorem faB_closed : closedAt 2 faB = true := rfl

/-- `faB[S/self][w/l]` for a closed handle `S`. -/
theorem faB_subst {S : Val} (hS : closedAt 0 S.1 = true) (w : Val) :
    (faB.subst 1 S).subst 0 w
      = .case (.val w) (.var 0) (.app (.val S) (.app (.val (.prim .free)) (.var 0))) := by
  have h₁ : ∀ d c, Expr.shift d c S.1 = S.1 := fun d c => shift_closedAt S.1 d hS (Nat.zero_le c)
  have h₂ : ∀ j s, Expr.subst j s S.1 = S.1 := fun j s => subst_closedAt S.1 s hS (Nat.zero_le j)
  simp [faB, Expr.subst, h₁, h₂]

/-- `freeAll`, a closed λ-value. -/
def freeAll : Val := fixV faB

/-- The postcondition of `F 1`. -/
abbrev unitQ : List SRec → Val → WProp := fun _ w => ⌜w = .unit⌝

/-- `freeAll v` frees every cell of a list `v` and returns `()`, at every record list. -/
theorem freeAll_wp {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : listRel b ls δ v ρ) (ls' : List SRec) :
    wpTS ls' (.app (.val freeAll) (.val v)) unitQ ρ := by
  have hS := selfV_closed faB_closed
  refine listRel_ind
    (P := fun _ _ _ v ρ => ∀ ls', wpTS ls' (.app (.val freeAll) (.val v)) unitQ ρ) ?_
    b ls δ v ρ h ls'
  rintro b ls δ v ρ (⟨v₁, hs⟩ | ⟨v₂, hs⟩) ls'
  · obtain ⟨rfl, rfl, rfl⟩ := pure_sep_iff.mp hs
    rw [freeAll, fixV_eq faB_closed]
    refine wpTS_lolli _ _ _ _ _ ?_
    rw [faB_subst hS]
    refine wpTS_sum₁ _ _ _ _ _ _ ?_
    exact wpTS_val _ _ _ _ ⟨rfl, rfl⟩
  · obtain ⟨rfl, ℓ, v', hs'⟩ := pure_sep_iff.mp hs
    obtain ⟨rfl, ρ₁, ρ₂, hc, hρ₁, hP⟩ := pure_sep_iff.mp hs'
    rw [freeAll, fixV_eq faB_closed]
    refine wpTS_lolli _ _ _ _ _ ?_
    rw [faB_subst hS]
    refine wpTS_sum₂ _ _ _ _ _ _ ?_
    have e₂ : (Expr.app (.val (selfV faB)) (.app (.val (.prim .free)) (.var 0))).subst 0
        (Val.loc ℓ) = (Kont.appR (.val (selfV faB)) .hole).plug
          (.app (.val (.prim .free)) (.val (.loc ℓ))) := by
      simp [Expr.subst, val_subst_closed hS, Kont.plug]
    rw [e₂]
    refine wpTS_bind _ _ _ _ _ ?_
    refine wpTS_free _ _ _ _ _ ⟨ρ₁, ρ₂, hc, hρ₁, ?_⟩
    have := hP ls'
    rw [freeAll] at this
    exact wpTS_selfV faB_closed v' ls' unitQ ρ₂ this

/-- `vC true (U (L ⊸ F 1))`, with `listRel` at `L`: `vC`'s `U`, `⊸` and `F` clauses. -/
def vLolliL (ls : List SRec) (δ : LSub) (f : Val) : WProp := fun ρ =>
  ∀ ls', Ext ls ls' ρ → ∀ v,
    (listRel true ls' δ v ─⋆ wpTS ls' (.app (.val f) (.val v)) fun ls'' => vC true .unit ls'' δ) ρ

/-- **`freeAll : U(L ⊸ F 1)`**, at every record list and lifetime substitution. -/
theorem freeAll_sem (ls : List SRec) (δ : LSub) : vLolliL ls δ freeAll PMap.empty := by
  intro ls' _ v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  exact freeAll_wp hv ls'

/-- `freeAll` as a value judgment: `return freeAll` at `F (U(L ⊸ F 1))`. -/
theorem freeAll_semV (ls : List SRec) (δ : LSub) :
    wpTS ls (.val freeAll) (fun ls' => vLolliL ls' δ) PMap.empty :=
  wpTS_val ls freeAll _ PMap.empty (freeAll_sem ls δ)

/-! ### Build a 3-cell list and free it -/

/-- `inj₂ (alloc (inj₂ (alloc (inj₂ (alloc (inj₁ ()))))))`. -/
def build3 : Expr :=
  .inj₂ (.app (.val (.prim .alloc)) (.inj₂ (.app (.val (.prim .alloc))
    (.inj₂ (.app (.val (.prim .alloc)) (.inj₁ (.val .unit)))))))

/-- `build3 : approx 3`, a `CDerives` derivation. -/
theorem build3_derives : CDerives LifeCtx.empty [] build3 (.val (approx 3)) :=
  .sumI₂ (.lolliE .nil (.sumI₂ (.lolliE .nil (.sumI₂ (.lolliE .nil (.sumI₁ (.unitI .nil))
    (.alloc .nil))) (.alloc .nil))) (.alloc .nil))

/-- `freeAll build3`. -/
def build3Free : Expr := .app (.val freeAll) build3

theorem build3Free_wp : wpTS [] build3Free (fun _ v => Fig16.BoLo.pure (v = Val.unit))
    (PMap.empty : WRes) := by
  have hb := fundamentalC build3_derives LSub.empty [] [] PMap.empty Adequacy.models_empty
    (gDenC_nil _ _)
  rw [show substAll [] build3 = build3 from Adequacy.psub_nil 0 build3] at hb
  refine wpTS_bind (.appR (.val freeAll) .hole) build3 [] _ PMap.empty ?_
  refine wpTS_mono (fun ls' v ρ hv => ?_) PMap.empty hb
  exact freeAll_wp (listRel_of_approx 3 hv) ls'

/-- **Adequacy at the list**: build a 3-cell list and free it; the run goes from the empty
memory to `()` and the empty memory. -/
theorem build3Free_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem build3Free Adequacy.emptyMem (.val .unit) := by
  obtain ⟨v, hsteps, hv⟩ := theorem32 build3Free (· = Val.unit) build3Free_wp
  subst hv
  exact hsteps

/-- The executable interpreter agrees: `()` and no cell left. -/
theorem build3Free_eval : Programs.unitNoLeak (eval build3Free) = true := by decide

end BoCa.Fig16.LogRel.CBPVWorld.Recursion

end
