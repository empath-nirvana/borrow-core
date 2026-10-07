import Core.EffBorrow
import Targets.A.EffAlg
import Targets.Base.Rows

/-!
# The Instance — our row forms, as instances of A's effect algebra (RESTRUCTURE §4.1)

The minimal open-row form `orowAlg Ξ` (a closed first-match prefix and an optional tail variable,
Rémy) and the closed rows `closedRowAlg Ξ` are instances of A's `EffAlg`; a row form `RowForm`
gives an algebra at each effect context with its reading as closed rows, and `RowLink` says the
algebra's operations are the closed-row operations the typing rules use.  `orowAlg_laws`,
`orowAlg_safe`, `rowLink_orowRF`: our rows meet Def. 3.5 and Def. 5.1 (A's S1, at the algebra).
`orowRF` is the minimal tail-variable form, fixed in done until OQ-13's remaining question.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont hndE raiseE cancelVal ccatchE)

/-- A row with an optional tail variable (Rémy): a closed first-match prefix `ops`, then the row
the variable `tail` stands for. -/
structure ORow where
  ops  : Row
  tail : Option RVar

/-- **A closed row tied to the effect context** (decision D1): every operation the row finds is a
label's, at the signature `Ξ` declares.  A label is a name that is not the reserved `0` and whose
signature is at most `2³²` operations long (operations are numbered by `UInt32`). -/
def RowAt (Ξ : EffCtx) (S : Row) : Prop :=
  ∀ n i o, Row.find S n i = some o →
    n ≠ 0 ∧ (Ξ n).length ≤ 2 ^ 32 ∧ (Ξ n)[i.toNat]? = some (o.q, o.A, o.B)

open Classical in
/-- **The minimal open-row form**: `⊙` is defined when the left row has no tail, or the right row
is empty, as for Yoshioka's simple rows; `∼` is equal tails and equal first-match lookup, so a
duplicate entry is shadowed as `Row.find` shadows it.  Reducible, so that its carrier is `ORow` to
every tactic. -/
@[reducible] def orowAlg (Ξ : EffCtx) : A.EffAlg where
  Lab := {n : UInt32 // n ≠ 0 ∧ Ξ n ≠ [] ∧ (Ξ n).length ≤ 2 ^ 32}
  Eff := ORow
  Var := RVar
  WF Γ ε := (∀ ρ, ε.tail = some ρ → ρ ∈ Γ) ∧ RowAt Ξ ε.ops
  WFLab _ _ := True
  comp ε₁ ε₂ := match ε₁.tail with
    | none => some ⟨ε₁.ops ++ ε₂.ops, ε₂.tail⟩
    | some _ => if ε₂.ops = [] ∧ ε₂.tail = none then some ε₁ else none
  unit := ⟨[], none⟩
  lift n := ⟨Row.ofEff n.1 (Ξ n.1) 0, none⟩
  eqv ε₁ ε₂ := ε₁.tail = ε₂.tail ∧ RowEq ε₁.ops ε₂.ops
  subst ρ S ε := if ε.tail = some ρ then ⟨ε.ops ++ S.ops, S.tail⟩ else ε

/-- The closed rows: the sub-algebra with no row variable.  Reducible, as `orowAlg`. -/
@[reducible] def closedRowAlg (Ξ : EffCtx) : A.EffAlg where
  Lab := {n : UInt32 // n ≠ 0 ∧ Ξ n ≠ [] ∧ (Ξ n).length ≤ 2 ^ 32}
  Eff := Row
  Var := Empty
  WF _ S := RowAt Ξ S
  WFLab _ _ := True
  comp S S' := some (S ++ S')
  unit := []
  lift n := Row.ofEff n.1 (Ξ n.1) 0
  eqv := RowEq
  subst α _ _ := α.elim

/-- A row form: an effect algebra at each effect context, its labels' names, and its reading of an
effect, at an environment of its variables, as a closed row. -/
structure RowForm where
  alg  : EffCtx → A.EffAlg
  name : ∀ Ξ, (alg Ξ).Lab → UInt32
  den  : ∀ Ξ, (alg Ξ).Eff → ((alg Ξ).Var → Row) → Row

/-- **The link**: the algebra's `⊙`, `0`, `(n)↑`, `∼`, substitution and `<` are the closed-row
`++`, `[]`, `Row.ofEff`, `RowEq`, environment update and `RowLe` that the typing rules use; and the
algebra covers every name, every closed row and every row variable. -/
structure RowLink (RF : RowForm) : Prop where
  comp  : ∀ Ξ ε₁ ε₂ ε η, (RF.alg Ξ).comp ε₁ ε₂ = some ε →
            RowEq (RF.den Ξ ε η) (RF.den Ξ ε₁ η ++ RF.den Ξ ε₂ η)
  unit  : ∀ Ξ η, RF.den Ξ (RF.alg Ξ).unit η = []
  lift  : ∀ Ξ L η, RowEq (RF.den Ξ ((RF.alg Ξ).lift L) η)
            (Row.ofEff (RF.name Ξ L) (Ξ (RF.name Ξ L)) 0)
  eqv   : ∀ Ξ ε₁ ε₂ η, (RF.alg Ξ).eqv ε₁ ε₂ → RowEq (RF.den Ξ ε₁ η) (RF.den Ξ ε₂ η)
  subst : ∀ Ξ α S ε (η η' : (RF.alg Ξ).Var → Row), η' α = RF.den Ξ S η →
            (∀ β, β ≠ α → η' β = η β) →
            RowEq (RF.den Ξ ((RF.alg Ξ).subst α S ε) η) (RF.den Ξ ε η')
  sub   : ∀ Ξ ε₁ ε₂, (RF.alg Ξ).Sub ε₁ ε₂ → ∀ η, RowLe (RF.den Ξ ε₁ η) (RF.den Ξ ε₂ η)
  names : ∀ Ξ (n : UInt32), n ≠ 0 → Ξ n ≠ [] → (Ξ n).length ≤ 2 ^ 32 → ∃ L, RF.name Ξ L = n
  rows  : ∀ Ξ (S : Row), (closedRowAlg Ξ).WF [] S → ∃ ε, ∀ η, RowEq (RF.den Ξ ε η) S
  vars  : ∀ Ξ (α : (RF.alg Ξ).Var), ∃ ε, ∀ η, RF.den Ξ ε η = η α

/-- The minimal open-row form, the restricted instance. -/
@[reducible] def orowRF : RowForm where
  alg := orowAlg
  name _ n := n.1
  den _ ε η := ε.ops ++ (match ε.tail with | none => [] | some ρ => η ρ)


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Steps Step1)

/-- **T0**: the row form's algebra is an effect algebra (Def. 3.5) that meets the safety conditions
(Def. 5.1), at every effect context.  In `EndStateAt` beside `RowLink RF`. -/
def RowAlgSafe (RF : RowForm) : Prop := ∀ Ξ : EffCtx, (RF.alg Ξ).Laws ∧ (RF.alg Ξ).Safe


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core

theorem rowEq_refl (S : Row) : RowEq S S := fun _ _ => rfl

theorem rowEq_symm {S S' : Row} (h : RowEq S S') : RowEq S' S := fun n i => (h n i).symm

theorem rowEq_trans {S S' S'' : Row} (h : RowEq S S') (h' : RowEq S' S'') : RowEq S S'' :=
  fun n i => (h n i).trans (h' n i)

theorem rowEq_equiv : Equivalence RowEq := ⟨rowEq_refl, rowEq_symm, rowEq_trans⟩

theorem rowEq_append {S₁ S₂ S₁' S₂' : Row} (h₁ : RowEq S₁ S₁') (h₂ : RowEq S₂ S₂') :
    RowEq (S₁ ++ S₂) (S₁' ++ S₂') := fun n i => by
  rw [Row.find_append, Row.find_append, h₁ n i, h₂ n i]

theorem rowEq_of_eq {S S' : Row} (h : S = S') : RowEq S S' := h ▸ rowEq_refl S

theorem find_nil (n i : UInt32) : Row.find [] n i = none := rfl

theorem rowAt_nil (Ξ : EffCtx) : RowAt Ξ [] := fun _ _ _ h => by simp [Row.find] at h

/-- Two rows tied to `Ξ` append to one. -/
theorem rowAt_append {Ξ : EffCtx} {S S' : Row} (h : RowAt Ξ S) (h' : RowAt Ξ S') :
    RowAt Ξ (S ++ S') := by
  intro n i o hf
  rw [Row.find_append] at hf
  cases hS : Row.find S n i with
  | none => rw [hS, Option.none_or] at hf; exact h' n i o hf
  | some o' => rw [hS, Option.some_or] at hf; cases hf; exact h n i o hS

/-- A row below a row tied to `Ξ` is tied to `Ξ`. -/
theorem rowAt_of_le {Ξ : EffCtx} {S S' : Row} (hle : RowLe S S') (h : RowAt Ξ S') : RowAt Ξ S :=
  fun n i o hf => h n i o (hle n i o hf)

/-- The prefix of a row tied to `Ξ`, read with its tail empty, is tied to `Ξ`. -/
theorem rowAt_left {Ξ : EffCtx} {S S' : Row} (h : RowAt Ξ (S ++ S')) : RowAt Ξ S :=
  rowAt_of_le (fun n i o hf => by rw [Row.find_append, hf, Option.some_or]) h

/-- A signature's row finds its first operation. -/
theorem find_ofEff_zero (n : UInt32) {E : List (Qual × VTy × VTy)} (hE : E ≠ []) :
    ∃ o, Row.find (Row.ofEff n E 0) n 0 = some o := by
  cases E with
  | nil => exact absurd rfl hE
  | cons p E => exact ⟨⟨n, 0, p.1, p.2.1, p.2.2⟩, by simp [Row.ofEff, Row.find]⟩

/-- A signature's row is well formed at its effect context. -/
theorem ofEff_wf (Ξ : EffCtx) (n : UInt32) (hn : n ≠ 0) (hlen : (Ξ n).length ≤ 2 ^ 32) :
    RowAt Ξ (Row.ofEff n (Ξ n) 0) := by
  intro m i o h
  obtain ⟨rfl, j, hj, rfl, rfl⟩ := Row.find_ofEff n (Ξ n) 0 m i o h
  refine ⟨hn, hlen, ?_⟩
  have hj' : (UInt32.ofNat (0 + j)).toNat = j := by
    rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  rw [hj']
  simp [List.getElem?_eq_getElem hj]

/-- Lookup in a signature's row at another name. -/
theorem find_ofEff_other {n m : UInt32} (E : List (Qual × VTy × VTy)) (h : m ≠ n) (i : UInt32) :
    Row.find (Row.ofEff n E 0) m i = none := Row.find_ofEff_ne n E 0 m i h

/-- `(L)↑ ⊙ ε₀ ∼ ε₂`, `L′ ≠ L`, `(L′)↑ ⊙ ε′ ∼ ε₂`: then `(L)↑ ⊙ ε′ ∼ ε′`. -/
theorem rowEq_lift_absorb {n n' : UInt32} {E E' : List (Qual × VTy × VTy)} {ε₀ ε' ε₂ : Row}
    (h₀ : RowEq (Row.ofEff n E 0 ++ ε₀) ε₂) (h' : RowEq (Row.ofEff n' E' 0 ++ ε') ε₂)
    (hne : n ≠ n') : RowEq (Row.ofEff n E 0 ++ ε') ε' := by
  intro m i
  rw [Row.find_append]
  by_cases hm : m = n
  · subst hm
    have e₁ := h₀ m i
    have e₂ := h' m i
    rw [Row.find_append] at e₁ e₂
    rw [find_ofEff_other E' hne i, Option.none_or] at e₂
    cases hf : Row.find (Row.ofEff m E 0) m i with
    | none => rfl
    | some o =>
        rw [hf, Option.some_or] at e₁
        rw [Option.some_or, e₂]
        exact e₁
  · rw [find_ofEff_other E hm i, Option.none_or]

theorem closedRowAlg_laws (Ξ : EffCtx) : (closedRowAlg Ξ).Laws where
  comp_wf Γ ε₁ ε₂ ε h₁ h₂ hc := by
    have hc' : ε₁ ++ ε₂ = ε := Option.some.inj hc
    subst hc'
    intro n i o hf
    rw [Row.find_append] at hf
    cases hf₁ : Row.find ε₁ n i with
    | none => rw [hf₁, Option.none_or] at hf; exact h₂ n i o hf
    | some o₁ => rw [hf₁, Option.some_or] at hf; cases hf; exact h₁ n i o hf₁
  unit_wf Γ := fun n i o h => by simp [Row.find] at h
  lift_wf Γ L _ := ofEff_wf Ξ L.1 L.2.1 L.2.2.2
  eqv_equiv := rowEq_equiv
  eqv_wf ε₁ ε₂ h Γ :=
    ⟨fun hw n i o hf => hw n i o ((h n i).trans hf),
      fun hw n i o hf => hw n i o ((h n i).symm.trans hf)⟩
  unit_r ε := ⟨ε ++ [], rfl, rowEq_of_eq (List.append_nil ε)⟩
  unit_l ε := ⟨[] ++ ε, rfl, rowEq_of_eq (List.nil_append ε)⟩
  assoc ε₁ ε₂ ε₃ _ := ⟨_, _, _, _, rfl, rfl, rfl, rfl, rowEq_of_eq (List.append_assoc _ _ _)⟩
  subst_comp α := α.elim
  subst_lift α := α.elim
  subst_eqv α := α.elim

theorem closedRowAlg_safe (Ξ : EffCtx) : (closedRowAlg Ξ).Safe where
  c1 L := by
    rintro ⟨ε, x, hc, hx⟩
    have hc' : Row.ofEff L.1 (Ξ L.1) 0 ++ ε = x := Option.some.inj hc
    subst hc'
    obtain ⟨o, ho⟩ := find_ofEff_zero L.1 L.2.2.1
    have := hx L.1 0
    rw [Row.find_append, ho, Option.some_or] at this
    simp [Row.find] at this
  c2 L L' ε ε' x := by
    rintro ⟨ε₀, x₀, hc₀, hx₀⟩ hc hx hne
    have hc₀' : Row.ofEff L.1 (Ξ L.1) 0 ++ ε₀ = x₀ := Option.some.inj hc₀
    have hc' : Row.ofEff L'.1 (Ξ L'.1) 0 ++ ε' = x := Option.some.inj hc
    subst hc₀' hc'
    exact ⟨ε', _, rfl, rowEq_lift_absorb hx₀ hx (fun h => hne (Subtype.ext h))⟩

/-- `orowAlg`'s `⊙`, unfolded. -/
theorem orow_comp_none {Ξ : EffCtx} {ε₁ ε₂ : ORow} (h : ε₁.tail = none) :
    (orowAlg Ξ).comp ε₁ ε₂ = some ⟨ε₁.ops ++ ε₂.ops, ε₂.tail⟩ := by
  simp [orowAlg, h]

theorem orow_comp_some {Ξ : EffCtx} {ε₁ ε₂ : ORow} {ρ : RVar} (h : ε₁.tail = some ρ) :
    (orowAlg Ξ).comp ε₁ ε₂ = if ε₂.ops = [] ∧ ε₂.tail = none then some ε₁ else none := by
  simp [orowAlg, h]

theorem orow_ext {ε ε' : ORow} (h₁ : ε.ops = ε'.ops) (h₂ : ε.tail = ε'.tail) : ε = ε' := by
  cases ε; cases ε'; simp_all

theorem orowAlg_laws (Ξ : EffCtx) : (orowAlg Ξ).Laws where
  comp_wf Γ ε₁ ε₂ ε h₁ h₂ hc := by
    cases ht : ε₁.tail with
    | none =>
        rw [orow_comp_none ht, Option.some.injEq] at hc
        subst hc
        refine ⟨h₂.1, fun n i o hf => ?_⟩
        rw [Row.find_append] at hf
        cases hf₁ : Row.find ε₁.ops n i with
        | none => rw [hf₁, Option.none_or] at hf; exact h₂.2 n i o hf
        | some o₁ => rw [hf₁, Option.some_or] at hf; cases hf; exact h₁.2 n i o hf₁
    | some ρ =>
        rw [orow_comp_some ht] at hc
        split at hc
        · cases hc; exact h₁
        · cases hc
  unit_wf Γ := ⟨(fun _ h => nomatch h), fun n i o h => by simp [Row.find] at h⟩
  lift_wf Γ L _ := ⟨(fun _ h => nomatch h), ofEff_wf Ξ L.1 L.2.1 L.2.2.2⟩
  eqv_equiv := ⟨fun ε => ⟨rfl, rowEq_refl _⟩, fun h => ⟨h.1.symm, rowEq_symm h.2⟩,
    fun h h' => ⟨h.1.trans h'.1, rowEq_trans h.2 h'.2⟩⟩
  eqv_wf ε₁ ε₂ h Γ := by
    obtain ⟨ht, hr⟩ := h
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun ρ e => h₁ ρ (ht.trans e), fun n i o hf => h₂ n i o ((hr n i).trans hf)⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun ρ e => h₁ ρ (ht.symm.trans e), fun n i o hf => h₂ n i o ((hr n i).symm.trans hf)⟩
  unit_r ε := by
    cases ht : ε.tail with
    | none =>
        refine ⟨⟨ε.ops ++ [], none⟩, ?_, ?_, rowEq_of_eq (List.append_nil _)⟩
        · rw [orow_comp_none ht]
        · exact ht.symm
    | some ρ =>
        refine ⟨ε, ?_, rfl, rowEq_refl _⟩
        rw [orow_comp_some ht]; simp [orowAlg]
  unit_l ε := ⟨⟨[] ++ ε.ops, ε.tail⟩, by rw [orow_comp_none rfl], rfl,
    rowEq_of_eq (List.nil_append _)⟩
  assoc ε₁ ε₂ ε₃ hdef := by
    cases ht₁ : ε₁.tail with
    | none =>
        cases ht₂ : ε₂.tail with
        | none =>
            refine ⟨⟨ε₁.ops ++ ε₂.ops, ε₂.tail⟩, ⟨(ε₁.ops ++ ε₂.ops) ++ ε₃.ops, ε₃.tail⟩,
              ⟨ε₂.ops ++ ε₃.ops, ε₃.tail⟩, ⟨ε₁.ops ++ (ε₂.ops ++ ε₃.ops), ε₃.tail⟩,
              orow_comp_none ht₁, orow_comp_none (by simpa using ht₂), orow_comp_none ht₂,
              orow_comp_none ht₁, rfl, rowEq_of_eq (List.append_assoc _ _ _)⟩
        | some ρ =>
            rcases hdef with ⟨x, y, hx, hy⟩ | ⟨x, y, hx, hy⟩
            · rw [orow_comp_none ht₁, Option.some.injEq] at hx
              subst hx
              rw [orow_comp_some (by simpa using ht₂)] at hy
              split at hy
              · rename_i h₃
                cases hy
                refine ⟨_, _, ε₂, _, orow_comp_none ht₁, ?_, ?_, orow_comp_none ht₁, rfl,
                  rowEq_refl _⟩
                · rw [orow_comp_some (by simpa using ht₂)]; simp [h₃]
                · rw [orow_comp_some ht₂]; simp [h₃]
              · cases hy
            · rw [orow_comp_some ht₂] at hx
              split at hx
              · rename_i h₃
                cases hx
                refine ⟨_, _, ε₂, _, orow_comp_none ht₁, ?_, ?_, orow_comp_none ht₁, rfl,
                  rowEq_refl _⟩
                · rw [orow_comp_some (by simpa using ht₂)]; simp [h₃]
                · rw [orow_comp_some ht₂]; simp [h₃]
              · cases hx
    | some ρ =>
        have hempty : ε₂.ops = [] ∧ ε₂.tail = none ∧ ε₃.ops = [] ∧ ε₃.tail = none := by
          rcases hdef with ⟨x, y, hx, hy⟩ | ⟨x, y, hx, hy⟩
          · rw [orow_comp_some ht₁] at hx
            split at hx
            · rename_i h₂
              cases hx
              rw [orow_comp_some ht₁] at hy
              split at hy
              · rename_i h₃; exact ⟨h₂.1, h₂.2, h₃.1, h₃.2⟩
              · cases hy
            · cases hx
          · cases ht₂ : ε₂.tail with
            | none =>
                rw [orow_comp_none ht₂, Option.some.injEq] at hx
                subst hx
                rw [orow_comp_some ht₁] at hy
                split at hy
                · rename_i h₃
                  simp only [List.append_eq_nil_iff] at h₃
                  exact ⟨h₃.1.1, rfl, h₃.1.2, h₃.2⟩
                · cases hy
            | some ρ' =>
                rw [orow_comp_some ht₂] at hx
                split at hx
                · cases hx
                  rw [orow_comp_some ht₁] at hy
                  split at hy
                  · rename_i h₃; rw [ht₂] at h₃; cases h₃.2
                  · cases hy
                · cases hx
        obtain ⟨h₂o, h₂t, h₃o, h₃t⟩ := hempty
        refine ⟨ε₁, ε₁, ⟨ε₂.ops ++ ε₃.ops, ε₃.tail⟩, ε₁, ?_, ?_, ?_, ?_, rfl, rowEq_refl _⟩
        · rw [orow_comp_some ht₁]; simp [h₂o, h₂t]
        · rw [orow_comp_some ht₁]; simp [h₃o, h₃t]
        · rw [orow_comp_none h₂t]
        · rw [orow_comp_some ht₁]; simp [h₂o, h₃o, h₃t]
  subst_comp α S ε₁ ε₂ ε _ hc := by
    cases ht₁ : ε₁.tail with
    | none =>
        rw [orow_comp_none ht₁, Option.some.injEq] at hc
        subst hc
        have hs₁ : (orowAlg Ξ).subst α S ε₁ = ε₁ := by simp [orowAlg, ht₁]
        rw [hs₁, orow_comp_none ht₁]
        by_cases ht₂ : ε₂.tail = some α
        · simp [orowAlg, ht₂, List.append_assoc]
        · simp [orowAlg, ht₂]
    | some ρ =>
        rw [orow_comp_some ht₁] at hc
        split at hc
        · rename_i h₂
          cases hc
          have hs₂ : (orowAlg Ξ).subst α S ε₂ = ε₂ := by simp [orowAlg, h₂.2]
          rw [hs₂]
          by_cases hρ : ρ = α
          · subst hρ
            cases hS : S.tail with
            | none =>
                have : (orowAlg Ξ).subst ρ S ε₁ = ⟨ε₁.ops ++ S.ops, S.tail⟩ := by
                  simp [orowAlg, ht₁]
                rw [this, orow_comp_none (by simpa using hS)]
                congr 1
                exact orow_ext (by simp [h₂.1]) (by simp [h₂.2, hS])
            | some ρ' =>
                have : (orowAlg Ξ).subst ρ S ε₁ = ⟨ε₁.ops ++ S.ops, S.tail⟩ := by
                  simp [orowAlg, ht₁]
                rw [this, orow_comp_some (by simpa using hS)]
                simp [h₂.1, h₂.2]
          · have : (orowAlg Ξ).subst α S ε₁ = ε₁ := by simp [orowAlg, ht₁, hρ]
            rw [this, orow_comp_some ht₁]
            simp [h₂.1, h₂.2]
        · cases hc
  subst_lift α S L _ := by simp [orowAlg]
  subst_eqv α S ε₁ ε₂ _ h := by
    obtain ⟨ht, hr⟩ := h
    by_cases h₁ : ε₁.tail = some α
    · have h₂ : ε₂.tail = some α := ht ▸ h₁
      have e₁ : (orowAlg Ξ).subst α S ε₁ = ⟨ε₁.ops ++ S.ops, S.tail⟩ := if_pos h₁
      have e₂ : (orowAlg Ξ).subst α S ε₂ = ⟨ε₂.ops ++ S.ops, S.tail⟩ := if_pos h₂
      rw [e₁, e₂]
      exact ⟨rfl, rowEq_append hr (rowEq_refl _)⟩
    · have h₂ : ¬ ε₂.tail = some α := ht ▸ h₁
      have e₁ : (orowAlg Ξ).subst α S ε₁ = ε₁ := if_neg h₁
      have e₂ : (orowAlg Ξ).subst α S ε₂ = ε₂ := if_neg h₂
      rw [e₁, e₂]
      exact ⟨ht, hr⟩

theorem orowAlg_safe (Ξ : EffCtx) : (orowAlg Ξ).Safe where
  c1 L := by
    rintro ⟨ε, x, hc, hx⟩
    rw [orow_comp_none rfl, Option.some.injEq] at hc
    subst hc
    obtain ⟨o, ho⟩ := find_ofEff_zero L.1 L.2.2.1
    have := hx.2 L.1 0
    simp only at this
    rw [Row.find_append, ho, Option.some_or] at this
    simp [Row.find] at this
  c2 L L' ε ε' x := by
    rintro ⟨ε₀, x₀, hc₀, hx₀⟩ hc hx hne
    rw [orow_comp_none rfl, Option.some.injEq] at hc₀ hc
    subst hc₀ hc
    refine ⟨ε', _, orow_comp_none rfl, rfl, ?_⟩
    exact rowEq_lift_absorb hx₀.2 hx.2 (fun h => hne (Subtype.ext h))

/-- **T0 at the minimal open-row form.** -/
theorem rowAlgSafe_orowRF : RowAlgSafe orowRF := fun Ξ => ⟨orowAlg_laws Ξ, orowAlg_safe Ξ⟩

/-- **T0 at the closed rows.** -/
theorem closedRowAlg_lawsSafe (Ξ : EffCtx) : (closedRowAlg Ξ).Laws ∧ (closedRowAlg Ξ).Safe :=
  ⟨closedRowAlg_laws Ξ, closedRowAlg_safe Ξ⟩

/-- The row a tail stands for. -/
theorem orowRF_den (Ξ : EffCtx) (ε : ORow) (η : RVar → Row) :
    orowRF.den Ξ ε η = ε.ops ++ (match ε.tail with | none => [] | some ρ => η ρ) := rfl

theorem rowLink_orowRF : RowLink orowRF where
  comp Ξ ε₁ ε₂ ε η hc := by
    cases ht : ε₁.tail with
    | none =>
        change (orowAlg Ξ).comp ε₁ _ = some _ at hc
        rw [orow_comp_none ht, Option.some.injEq] at hc
        subst hc
        simp only [ht, List.append_nil]
        exact rowEq_of_eq (List.append_assoc _ _ _)
    | some ρ =>
        change (orowAlg Ξ).comp ε₁ _ = some _ at hc
        rw [orow_comp_some ht] at hc
        split at hc
        · rename_i h₂
          cases hc
          simp only [ht, h₂.1, h₂.2, List.append_nil]
          exact rowEq_refl _
        · cases hc
  unit Ξ η := rfl
  lift Ξ L η := by
    simp only [List.append_nil]
    exact rowEq_refl _
  eqv Ξ ε₁ ε₂ η h := by
    obtain ⟨ht, hr⟩ := h
    simp only [ht]
    exact rowEq_append hr (rowEq_refl _)
  subst Ξ α S ε η η' hα hβ := by
    by_cases h : ε.tail = some α
    · have : (orowRF.alg Ξ).subst α S ε = ⟨ε.ops ++ S.ops, S.tail⟩ := by
        simp [orowRF, orowAlg, h]
      rw [this]
      simp only [h, hα]
      exact rowEq_of_eq (List.append_assoc _ _ _)
    · have : (orowRF.alg Ξ).subst α S ε = ε := by simp [orowRF, orowAlg, h]
      rw [this]
      simp only
      cases ht : ε.tail with
      | none => exact rowEq_refl _
      | some β =>
          have hβα : β ≠ α := fun e => h (by rw [ht, e])
          simp only [hβ β hβα]
          exact rowEq_refl _
  sub Ξ ε₁ ε₂ hs η := by
    obtain ⟨ε, x, hc, hx⟩ := hs
    have hcomp : RowEq (orowRF.den Ξ x η) (orowRF.den Ξ ε₁ η ++ orowRF.den Ξ ε η) := by
      cases ht : ε₁.tail with
      | none =>
          change (orowAlg Ξ).comp ε₁ _ = some _ at hc
          rw [orow_comp_none ht, Option.some.injEq] at hc
          subst hc
          simp only [ht, List.append_nil]
          exact rowEq_of_eq (List.append_assoc _ _ _)
      | some ρ =>
          change (orowAlg Ξ).comp ε₁ _ = some _ at hc
          rw [orow_comp_some ht] at hc
          split at hc
          · rename_i h₂
            cases hc
            simp only [ht, h₂.1, h₂.2, List.append_nil]
            exact rowEq_refl _
          · cases hc
    have heqv : RowEq (orowRF.den Ξ x η) (orowRF.den Ξ ε₂ η) := by
      obtain ⟨ht, hr⟩ := hx
      simp only [ht]
      exact rowEq_append hr (rowEq_refl _)
    intro n i o hf
    rw [← heqv n i, hcomp n i, Row.find_append, hf, Option.some_or]
  names Ξ n hn hE hlen := ⟨⟨n, hn, hE, hlen⟩, rfl⟩
  rows Ξ S _ := ⟨⟨S, none⟩, fun η => rowEq_of_eq (List.append_nil S)⟩
  vars Ξ α := ⟨⟨[], some α⟩, fun η => rfl⟩

end Targets

end
