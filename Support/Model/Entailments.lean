import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas
import Paper.S6_4_StandardEntailments.Lemmas
import Support.Dynamics.Machine
import Support.Model.Algebra
import Support.Model.CellFacts
import Support.Model.Composition
import Support.Model.Flattening
import Support.Model.FlatteningCells
import Support.Model.Lifetimes
import Support.Model.Notation
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.Singletons
import Support.Model.Update

/-!
# Support — Model — Entailments

`[about ours]`.  What §6.5–§6.6's entailments need beyond the propositions: `⫤⊨` reflexive and extensional, a `●`-factor of a reborrowed `imm` cell and the clauses that admit it, `reb_α` at `∅` and its outlives bound, and the join-indexed conclusion 6.115's literal reading measures.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- A `●`-factor of an `imm` cell is `imm` over a subset of its lifetime set, at
the same value and witness.
`[about ours: the cell-level content of `[TR]` 6.43, read at one factor]` -/
theorem ResU.factor_imm_sub {ρ₁ ρ₂ ρ : ResU Loc Val} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ₁ : CellU Loc Val} (h₁ : ρ₁.get l = some ψ₁)
    {s : LSet} {v : Val} {χ : ResU Loc Val} {hχ : χ.InStratum s.join}
    (he : ρ.get l = some (CellU.immOf s v χ hχ)) :
    ∃ (t : LSet) (ht : χ.InStratum t.join), (∀ x, t.mem x → s.mem x) ∧
      ρ₁.get l = some (CellU.immOf t v χ ht) := by
  rcases ResU.Comp.get hc l with ⟨f₁, -, -⟩ | ⟨φ, f₁, -, f⟩ | ⟨φ, f₁, -, -⟩ |
      ⟨φa, φb, φ, f₁, -, f, hC⟩
  · rw [h₁] at f₁; exact absurd f₁ (by simp)
  · rw [he] at f
    exact ⟨s, hχ, fun _ h => h, f₁.trans f.symm⟩
  · rw [h₁] at f₁; exact absurd f₁ (by simp)
  · rw [he] at f
    obtain rfl := Option.some.inj f
    obtain ⟨s₁, s₂, w, ζ, k₁, k₂, k₃, e₁, -, e₃⟩ := hC
    obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₃
    exact ⟨s₁, k₁, fun x hx => Or.inl hx, f₁.trans (congrArg some e₁)⟩

/-- A nonempty subset of `{α}` is `{α}`, so an `imm` cell over it is the cell
`reb_α` writes at `{α}`. -/
theorem immOf_sub_singleton {α : Life} {t : LSet} {v : Val} {χ : ResU Loc Val}
    {ht : χ.InStratum t.join} (hts : ∀ x, t.mem x → (LSet.singleton α).mem x)
    (h : χ.InStratum (LSet.singleton α).join) :
    CellU.immOf t v χ ht = CellU.immOf (LSet.singleton α) v χ h := by
  have e : t = LSet.singleton α := LSet.ext fun x =>
    ⟨hts x, fun hx => by
      have hj : t.join = α := hts _ t.join_mem
      show t.mem x
      rw [show x = α from hx, ← hj]; exact t.join_mem⟩
  subst e; rfl

/-- `reb_α`'s body survives passing to a `●`-factor of the image, at every
location that factor defines: `[TR]` 6.127's closing substitution `ρ′ → ρ′₁`.
`[about ours: the `ρ′` half of `[TR]` 6.127's closing sentence, at our `reb_α`]` -/
theorem ResU.RebAt.factor {α : Life} {ρ ρ' ρ'₁ ρ'₂ : ResU Loc Val} {l : Loc}
    {p : ResU Loc Val} (h : ResU.RebAt α ρ ρ' l p) (hc : ResU.CompS ρ'₁ ρ'₂ ρ')
    {ψ : CellU Loc Val} (hψ : ρ'₁.get l = some ψ) : ResU.RebAt α ρ ρ'₁ l p := by
  refine ⟨h.1, fun v hv => ?_, fun b v χ hb P hw hm => ?_, fun s v χ hs hm => ?_⟩
  · obtain ⟨hh, he⟩ := h.2.1 v hv
    obtain ⟨t, ht, hts, e⟩ := ResU.factor_imm_sub hc hψ he
    exact ⟨hh, e.trans (congrArg some (immOf_sub_singleton hts hh))⟩
  · obtain ⟨⟨hh, he⟩, hd⟩ := h.2.2.1 b v χ hb P hw hm
    obtain ⟨t, ht, hts, e⟩ := ResU.factor_imm_sub hc hψ he
    exact ⟨⟨hh, e.trans (congrArg some (immOf_sub_singleton hts hh))⟩, hd⟩
  · obtain ⟨⟨t, ht, hts, he⟩, hd⟩ := h.2.2.2 s v χ hs hm
    obtain ⟨t', ht', hts', e⟩ := ResU.factor_imm_sub hc hψ he
    exact ⟨⟨t', ht', fun x hx => hts x (hts' x hx), e⟩, hd⟩

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

theorem BiEntails.refl (P : SPropU Loc Val) : P ⫤⊨ P := ⟨Entails.refl P, Entails.refl P⟩

/-- Two propositions that entail each other are equal. -/
theorem eq_of_biEntails {P Q : SPropU Loc Val} (h : P ⫤⊨ Q) : P = Q :=
  funext fun ρ => propext ⟨fun k => h.1 ρ k, fun k => h.2 ρ k⟩

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo

/-- `[TR]` 6.115 at the printed index `α ⊔ β`, over our `ptoImm`.
`[about ours: 6.115's printed conclusion index over the connective at `⊓β̄`]` -/
def IAgreeAtJoin : Prop :=
  ∀ (l : Nat) (α β : Life) (P Q : Nat → SPropU Nat Nat),
    (ptoImm l α P ⋆ ptoImm l β Q) ⊨ ptoImm l (α ⊔ β) (fun v => and (P v) (Q v))

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-- "To start, it only holds of resources `ρ` that live longer than `α`"
([CONF] §4.4, p. 415:23): `reb_α`'s first conjunct is `[α]`'s own. -/
theorem reborrow_outlives (α : Life) (P : SPropU Loc Val) :
    reborrow α P ⊨ (fun ρ => Outlives ρ α) := by
  rintro ρ ⟨ρ', ⟨ho, -⟩, -⟩
  exact ho

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo

/-- The singleton family `π = [(ℓ, p)]` has `(ℓ, p)` for its only member. -/
theorem memSingle {A B : Type} {a a' : A} {b b' : B} (hm : (a, b) ∈ [(a', b')]) :
    a = a' ∧ b = b' := by
  have he := List.mem_singleton.mp hm
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-- `∅ ∈ reb_α(∅)`, at every `α`. -/
theorem reb_empty (α : Life) :
    ResU.Reb α (PMap.empty : ResU Loc Val) PMap.empty := by
  refine ⟨fun l ψ e => absurd e (by simp), [], PMap.empty, ⟨by simp, fun l => ?_⟩,
    BigComp.nil, ResU.Le.refl _, fun l p hm => absurd hm (by simp)⟩
  simp

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

theorem noOwn_empty : NoOwn (PMap.empty : WRes) := by
  refine PMap.ext fun l => ?_
  show (Option.none.bind fun ψ =>
    if CellU.kind ψ = Kind.own then some ψ else none) = none
  rfl

/-- `ρ₁ # ρ₂` names the composite and its lowering.
`[about ours: the two applications of a printed `#` that §6.7 makes]` -/
theorem hash_lower {ρ₁ ρ₂ : WRes} (h : ResU.Hash ρ₁ ρ₂) :
    ∃ σ μ, ResU.CompS ρ₁ ρ₂ σ ∧ ResU.Valid σ ∧ ResU.Lower σ μ := by
  obtain ⟨-, σ, hσ, τ, hτ⟩ := h
  exact ⟨σ, fun l => (τ.get l).map CellU.erase, hσ, ⟨τ, hτ⟩, τ, hτ, fun _ => rfl⟩

/-- `wp`'s source memory may be taken as given: `⟦ρ_f ● ρ⟧` is defined and
unique.
`[about ours: the reading of `wp`'s own source memory]` -/
theorem wp_lower {e : Expr} {Q : Val → WProp} {ρ ρf fρ : WRes} {μ : Heap}
    (h : wp e Q ρ) (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ)
    (hl : ResU.Lower fρ μ) :
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (v : Val) (μ' : Heap),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      Steps μ e μ' (.val v) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
      NoOwn ρp ∧
      Q v ρ' := by
  obtain ⟨ρ', ρp, fσ, fρ', fρ'p, π, v, ν, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hC⟩ := h ρf hf
  cases ResU.CompS.functional h₄ hc
  cases ResU.Lower.functional h₅ hl
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ', h₁, h₂, h₃, h₆, h₇, h₈, h₉, hA, hB, hC⟩

/-- `⦇ρ ● ℓ↦own(v)⦈ = ⦇ρ⦈ ● ℓ↦own(v)`, as a Kleene equality.
`[about ours: the sentence `[TR]` 6.141–6.145 share, at the walks]` -/
theorem flat_compS_own {ρ ρ' τ : WRes} {l : BoCa.Loc} {v : Val}
    (hc : ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ') :
    ResU.Flat ρ' τ ↔
      ∃ σ, ResU.Flat ρ σ ∧ ResU.CompS σ (ResU.single l (CellU.ownOf v)) τ := by
  constructor
  · intro hτ
    obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hcτ⟩ :=
      (ResU.Flat.split hc).mp hτ
    cases ExS.functional he₂ (ExW.single_own l v)
    cases AgW.functional ha₂ (AgW.single_own l v)
    cases ResU.CompR.functional hac (ResU.comp_empty_right a₁)
    obtain ⟨x, hx, hxτ⟩ :=
      (ResU.CompS.assoc e₁ (ResU.single l (CellU.ownOf v)) a₁ τ).mpr ⟨e, hec, hcτ⟩
    obtain ⟨σ, hσ, hστ⟩ :=
      (ResU.CompS.assoc e₁ a₁ (ResU.single l (CellU.ownOf v)) τ).mp
        ⟨x, ResU.CompS.comm hx, hxτ⟩
    exact ⟨σ, ⟨e₁, a₁, he₁, ha₁, hσ⟩, hστ⟩
  · rintro ⟨σ, ⟨e₁, a₁, he₁, ha₁, hσ⟩, hστ⟩
    obtain ⟨x, hx, hxτ⟩ :=
      (ResU.CompS.assoc e₁ a₁ (ResU.single l (CellU.ownOf v)) τ).mpr ⟨σ, hσ, hστ⟩
    obtain ⟨e, hec, hcτ⟩ :=
      (ResU.CompS.assoc e₁ (ResU.single l (CellU.ownOf v)) a₁ τ).mp
        ⟨x, ResU.CompS.comm hx, hxτ⟩
    exact (ResU.Flat.split hc).mpr
      ⟨e₁, _, e, a₁, PMap.empty, a₁, he₁, ExW.single_own l v, hec, ha₁,
        AgW.single_own l v, ResU.comp_empty_right a₁, hcτ⟩

/-- A location held in `ρ`, at any tag, reads its value in every memory `ρ`
lowers to.  `[about ours: the lookup the operational steps of `[TR]`
6.143, 6.144 and 6.145 need]` -/
theorem lower_get {ρ : WRes} {μ : Heap} {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc BoCa.Val} (h : ResU.Lower ρ μ)
    (e : ρ.get l = some ψ) : μ l = some ψ.erase := by
  obtain ⟨τ, hτ, hval⟩ := h
  obtain ⟨χ, hχ, -, hv, -⟩ := hτ.get e
  rw [hval l, hχ]
  exact congrArg some hv

/-- A location owned in `ρ` reads its value in every memory `ρ` lowers to.
`[about ours: the lookup `[TR]` 6.143's and 6.145's
operational steps need]` -/
theorem lower_get_own {ρ : WRes} {μ : Heap} {l : BoCa.Loc} {v : Val}
    (h : ResU.Lower ρ μ) (e : ρ.get l = some (CellU.ownOf v)) : μ l = some v :=
  lower_get h e

/-- `⟦−⟧` is undefined exactly where its flattening is. -/
theorem lower_eq_none_iff {μ : Heap} {τ : WRes} {l : BoCa.Loc}
    (hval : ∀ k, μ k = (τ.get k).map CellU.erase) :
    μ l = none ↔ τ.get l = none := by
  rw [hval l]
  cases τ.get l <;> simp

/-- A location `⦇ρ⦈` misses is a location `ρ` misses.
`[about ours: the freshness `[TR]` 6.141's proof uses]` -/
theorem get_eq_none_of_flat {ρ τ : WRes} {l : BoCa.Loc}
    (hτ : ResU.Flat ρ τ) (hl : τ.get l = none) : ρ.get l = none := by
  cases f : ρ.get l with
  | none => rfl
  | some ψ =>
      obtain ⟨χ, hχ, -⟩ := hτ.get f
      exact absurd (hχ.symm.trans hl) (by simp)

/-- `ρ ▶◀ ℓ↦ψ` at a location `ρ` misses. -/
theorem compatS_single_of_get_none {ρ : WRes} {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc BoCa.Val} (hl : ρ.get l = none) :
    ResU.CompatS ρ (ResU.single l ψ) := by
  classical
  refine ResU.Compat.of_disjoint fun k => ?_
  by_cases e : k = l
  · exact Or.inl (e ▸ hl)
  · exact Or.inr (ResU.single_get_ne _ e)

/-- An owned cell excludes every other cell at its location.
`[about ours: `[TR]` Lemma 6.41 with the singleton replaced by any resource
carrying an `own` cell at `ℓ`]` -/
theorem get_eq_none_of_compatS_own {ρ σ : WRes} {l : BoCa.Loc} {v : Val}
    (h : ResU.CompatS ρ σ) (e : ρ.get l = some (CellU.ownOf v)) : σ.get l = none := by
  cases f : σ.get l with
  | none => rfl
  | some χ => exact absurd (CellU.CompatS.kinds (h l _ χ e f)).1 (by simp)

/-- `⟦ρ ● ℓ↦own(v)⟧ = ⟦ρ⟧ ⊎ ℓ↦v`, at a location the memory misses.
`[about ours: 6.141's "By definition, `⟦ρ_f ● ρ⟧ ⊎ ℓ↦v = ⟦ρ_f ● ρ ● ℓ↦own(v)⟧`"
at the walks]` -/
theorem lower_compS_own {ρ ρ' : WRes} {μ : Heap} {l : BoCa.Loc} {v : Val}
    (hc : ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ') (hμ : ResU.Lower ρ μ)
    (hl : μ l = none) : ResU.Lower ρ' (BoCa.BoLo.Heap.upd μ l v) := by
  classical
  obtain ⟨τ, hτ, hval⟩ := hμ
  have hτl : τ.get l = none := (lower_eq_none_iff hval).mp hl
  obtain ⟨t, ht⟩ := (ResU.compS_defined_iff τ (ResU.single l (CellU.ownOf v))).mpr
    (ResU.Compat.of_disjoint fun k => by
      by_cases e : k = l
      · exact Or.inl (e ▸ hτl)
      · exact Or.inr (ResU.single_get_ne _ e))
  refine ⟨t, (flat_compS_own hc).mpr ⟨τ, hτ, ht⟩, fun k => ?_⟩
  by_cases e : k = l
  · subst e
    rw [ResU.Comp.get_of_left_none ht hτl, ResU.single_get_self]
    simp [BoCa.BoLo.Heap.upd]
  · rw [ResU.Comp.get_of_right_none ht (ResU.single_get_ne _ e),
      BoCa.BoLo.Heap.upd_other e]
    exact hval k

/-- `⟦ρ ● ℓ↦own(v)⟧ = ⟦ρ⟧ ⊎ ℓ↦v`, read the other way.
`[about ours: 6.142's and 6.143's "By definition,
`⟦ρ_f ● ℓ↦own(v) ● ρ₂⟧ = ⟦ρ_f ● ρ₂⟧ ⊎ ℓ↦v`" at the walks]` -/
theorem lower_compS_own_inv {ρ ρ' : WRes} {μ' : Heap} {l : BoCa.Loc} {v : Val}
    (hc : ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ') (hμ : ResU.Lower ρ' μ') :
    μ' l = some v ∧
      ∃ μ, ResU.Lower ρ μ ∧ μ' = BoCa.BoLo.Heap.upd μ l v ∧ μ l = none := by
  classical
  obtain ⟨t, ht, hval⟩ := hμ
  obtain ⟨τ, hτ, hστ⟩ := (flat_compS_own hc).mp ht
  have hτl : τ.get l = none :=
    ResU.compatS_single_own (ResU.CompatS.symm hστ.1)
  have hvl : t.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_left_none hστ hτl, ResU.single_get_self]
  refine ⟨by rw [hval l, hvl]; rfl,
    fun k => (τ.get k).map CellU.erase, ⟨τ, hτ, fun _ => rfl⟩, ?_, by simp [hτl]⟩
  funext k
  by_cases e : k = l
  · subst e
    rw [hval k, hvl, BoCa.BoLo.Heap.upd_same]
    rfl
  · rw [hval k, BoCa.BoLo.Heap.upd_other e,
      ResU.Comp.get_of_right_none hστ (ResU.single_get_ne _ e)]

/-- `ρ ↭ ρ ● ℓ↦own(v)`: 6.141's "since `↭` ignores own cells".
`[about ours: the step "`↭` ignores own cells" that 6.141, 6.142 and 6.145
each take in one line]` -/
theorem updV_compS_own {ρ ρ' : WRes} {l : BoCa.Loc} {v : Val}
    (hc : ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ')
    (hv : ResU.Valid ρ) (hv' : ResU.Valid ρ') : ResU.UpdV ρ ρ' := by
  classical
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨t, ht⟩ := hv'
  obtain ⟨τ', hτ', hστ⟩ := (flat_compS_own hc).mp ht
  cases ResU.Flat.functional hτ' hτ
  have hτl : τ.get l = none := ResU.compatS_single_own (ResU.CompatS.symm hστ.1)
  have hget : ∀ k, k ≠ l → t.get k = τ.get k := fun k e =>
    ResU.Comp.get_of_right_none hστ (ResU.single_get_ne _ e)
  have hgetl : t.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_left_none hστ hτl, ResU.single_get_self]
  refine ⟨ResU.upd_of_flat hτ ht (fun k s w χ h => ?_) (fun k b P => ?_),
    ⟨τ, hτ⟩, ⟨t, ht⟩⟩
  · by_cases e : k = l
    · subst e
      rw [hτl, hgetl]
      exact ⟨fun hx => absurd hx (by simp), fun hx =>
        absurd (Option.some.inj hx) CellU.ownOf_ne_immOf⟩
    · rw [hget k e]
  · by_cases e : k = l
    · subst e
      rw [hτl, hgetl]
      exact ⟨fun ⟨_, _, _, _, hx⟩ => absurd hx (by simp),
        fun ⟨_, _, _, _, hx⟩ => absurd (Option.some.inj hx) CellU.ownOf_ne_mutOf⟩
    · rw [hget k e]

/-- `ρ_f # ρ ● ℓ↦own(v)` at a location `⟦ρ_f ● ρ⟧` misses, together with the
composite it names and that composite's memory.
`[about ours: the three obligations 6.141's and 6.145's chosen witnesses
share]` -/
theorem hash_compS_own {ρf ρ ρ' σ : WRes} {μ : Heap} {l : BoCa.Loc} {v : Val}
    (hσ : ResU.CompS ρf ρ σ) (hμ : ResU.Lower σ μ) (hl : μ l = none)
    (hc : ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ') :
    ∃ σ', ResU.CompS ρf ρ' σ' ∧ ResU.Hash ρf ρ' ∧
      ResU.Lower σ' (BoCa.BoLo.Heap.upd μ l v) := by
  classical
  obtain ⟨τ, hτ, hval⟩ := hμ
  obtain ⟨σ', hσ'⟩ := (ResU.compS_defined_iff σ (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none (get_eq_none_of_flat hτ ((lower_eq_none_iff hval).mp hl)))
  obtain ⟨x, hx, hxσ'⟩ :=
    (ResU.CompS.assoc ρf ρ (ResU.single l (CellU.ownOf v)) σ').mpr ⟨σ, hσ, hσ'⟩
  cases ResU.CompS.functional hx hc
  have hlow : ResU.Lower σ' (BoCa.BoLo.Heap.upd μ l v) :=
    lower_compS_own hσ' ⟨τ, hτ, hval⟩ hl
  obtain ⟨t, ht, -⟩ := id hlow
  exact ⟨σ', hxσ', ⟨hxσ'.1, σ', hxσ', ⟨t, ht⟩⟩, hlow⟩

/-- `Loc ≜ ℕ` is infinite.
`[about ours: the infinitude of `Loc`, which neither document states]` -/
theorem loc_infinite : PMap.Infinite BoCa.Loc := by
  have hub : ∀ (t : List BoCa.Loc) (l : BoCa.Loc), l ∈ t → l ≤ t.foldr max 0 := by
    intro t
    induction t with
    | nil => intro l hl; exact absurd hl (by simp)
    | cons a t ih =>
        intro l hl
        rcases List.mem_cons.mp hl with rfl | hl
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih l hl) (Nat.le_max_right _ _)
  intro d
  exact ⟨d.foldr max 0 + 1, fun hmem => Nat.not_succ_le_self _ (hub d _ hmem)⟩

/-- `∅ ∈ Res_β`. -/
theorem stratum_empty (b : Life) :
    ResU.InStratum (Loc := BoCa.Loc) (Val := BoCa.Val) b PMap.empty :=
  fun _ _ e => absurd e (by simp)

/-- "`⌜v = v′⌝ ⋆ P̂(v)` is equivalent to `P̂(v)`" (`[TR]` 6.144's proof, p. 37),
at a pure proposition that holds.
`[about ours: 6.144's own sentence, stated as the printed `⫤⊨`]` -/
theorem pure_sep_biEntails {p : Prop} (hp : p) (P : WProp) :
    BiEntails (sep (pure p) P) P := by
  constructor
  · rintro ρ ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, hP⟩
    rwa [eq_of_compS_empty_left hc]
  · exact fun ρ hP => ⟨PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, hp⟩, hP⟩

/-- A cell of one operand fixes the composite's value at its location.
`[about ours: the lookup `[TR]` 6.144's closing run performs without comment]` -/
theorem compS_get_erase {ρ₁ ρ₂ ρ : WRes} {l : BoCa.Loc}
    {ψ₁ : CellU BoCa.Loc BoCa.Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (e₁ : ρ₁.get l = some ψ₁) : ∃ ψ, ρ.get l = some ψ ∧ ψ.erase = ψ₁.erase := by
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    obtain rfl := Option.some.inj f₁
    exact ⟨_, f, rfl⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    obtain rfl := Option.some.inj f₁
    exact ⟨χ, f, (CellU.CompS.erase hC).1⟩

end BoCa.Fig16.BoLo

end
