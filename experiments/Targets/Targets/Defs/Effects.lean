import Core.EffBorrow

/-!
# Targets — what an effect is (DESIGN §2, D1–D4)

* **D1.** An operation is Core's `OpSig ⟨n, i, q, A, B⟩`; a row is Core's `Row` (a first-match
  list keyed by `(n, i)`); a signature is a name's operations `E : List (Qual × VTy × VTy)`; an
  effect context `Ξ` gives each name its signature.  A row variable `RVar` carries a constraint
  `RowCon`, and a judgment at a row context means every admissible closed instance
  (`RowCtx.Models`).  `Row.NU`: no operation the row's lookup finds is a resuming `unr` one (the
  end state is stated over the unr-free fragment, decision 63).
* **D2.** An effect algebra in Yoshioka–Sekiyama–Igarashi's sense (Def. 3.5), its data and its
  laws kept apart; the minimal open-row form `orowAlg` (a closed first-match prefix and an
  optional tail variable) and the closed rows `closedRowAlg`; a row form `RowForm` (an algebra at
  each effect context with its reading as closed rows), and `RowLink`, which says the algebra's
  operations are the closed-row operations the typing rules use.
* **D4.** The frozen finalisers of a context, `Kont.fins`, and the cancel branch `cancelOf`.

D3 (handlers) is Core's `hndVal`/`[handle]` and needs no new definition.
-/

noncomputable section

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont hndE raiseE cancelVal ccatchE)

/-! ### D1. Rows, row variables, row contexts -/

/-- A row variable. -/
abbrev RVar := Nat

/-- No operation the row's lookup finds is a resuming `unr` one (decision 63: the end state is
stated over the unr-free fragment).  Read through `Row.find`, as the row's protocol reads it. -/
def Row.NU (S : Row) : Prop := ∀ n i o, Row.find S n i = some o → o.abort = true ∨ o.q ≠ .unr

/-- The class of operations a row admits.  `.any` is every unr-free row. -/
inductive RowClass
  | abortive
  | resumeOnce
  | any
  deriving DecidableEq, Repr

/-- The rows of a class. -/
def RowClass.Admits : RowClass → Row → Prop
  | .abortive,   S => ∀ o ∈ S, o.abort = true
  | .resumeOnce, S => ∀ o ∈ S, o.abort = true ∨ o.q = .lin
  | .any,        S => Row.NU S

/-- The constraint a row variable carries: the class of its operations, and an admissibility
condition on each operation (OQ-56's question, at a row variable). -/
structure RowCon where
  cls : RowClass
  adm : OpSig → Prop

/-- A row context: the row variables in scope with their constraints. -/
abbrev RowCtx := List (RVar × RowCon)

/-- A row environment: each row variable is a closed row. -/
abbrev RowEnv := RVar → Row

/-- `η` is an admissible instance of `Θ`. -/
def RowCtx.Models (Θ : RowCtx) (η : RowEnv) : Prop :=
  ∀ ρ c, (ρ, c) ∈ Θ → c.cls.Admits (η ρ) ∧ ∀ o ∈ η ρ, c.adm o

/-- An effect context: each name's signature, its operations numbered from `0`. -/
abbrev EffCtx := UInt32 → List (Qual × VTy × VTy)

/-- Two rows with the same operations: equal first-match lookup. -/
def RowEq (S S' : Row) : Prop := ∀ n i, Row.find S n i = Row.find S' n i

/-- The row has the operation `i` of the name `n`. -/
def Row.Has (S : Row) (n i : UInt32) : Prop := (Row.find S n i).isSome

/-! ### D2. The effect algebra (for T0) -/

/-- An effect algebra's data (Yoshioka–Sekiyama–Igarashi Def. 3.5): labels, effects, variables,
well-formedness under the variables in scope, `⊙` (partial), `0`, `(L)↑`, `∼` and
substitution. -/
structure EffAlg where
  Lab   : Type
  Eff   : Type
  Var   : Type
  /-- `Γ ⊢ ε : Eff`, `Γ` the row variables in scope. -/
  WF    : List Var → Eff → Prop
  WFLab : List Var → Lab → Prop
  /-- `⊙`, partial. -/
  comp  : Eff → Eff → Option Eff
  /-- `0`. -/
  unit  : Eff
  /-- `(L)↑`. -/
  lift  : Lab → Eff
  /-- `∼`. -/
  eqv   : Eff → Eff → Prop
  /-- `subst α S ε` is `ε[S/α]`. -/
  subst : Var → Eff → Eff → Eff

/-- `α ↦ S ⊢ εs : Eff`: the effects are well formed with `α` in scope, and `S` where `α` is. -/
def EffAlg.SubstOK (EA : EffAlg) (α : EA.Var) (S : EA.Eff) (εs : List EA.Eff) : Prop :=
  ∃ Γ₁ Γ₂, (∀ ε ∈ εs, EA.WF (Γ₁ ++ α :: Γ₂) ε) ∧ EA.WF Γ₁ S

/-- **Def. 3.5**: the data form an effect algebra. -/
structure EffAlg.Laws (EA : EffAlg) : Prop where
  -- first bullet: `⊙`, `0` and `(−)↑` preserve well-formedness; `∼` is an equivalence that
  -- preserves it
  comp_wf   : ∀ Γ ε₁ ε₂ ε, EA.WF Γ ε₁ → EA.WF Γ ε₂ → EA.comp ε₁ ε₂ = some ε → EA.WF Γ ε
  unit_wf   : ∀ Γ, EA.WF Γ EA.unit
  lift_wf   : ∀ Γ L, EA.WFLab Γ L → EA.WF Γ (EA.lift L)
  eqv_equiv : Equivalence EA.eqv
  eqv_wf    : ∀ ε₁ ε₂, EA.eqv ε₁ ε₂ → ∀ Γ, (EA.WF Γ ε₁ ↔ EA.WF Γ ε₂)
  -- second bullet: a partial monoid under `∼`
  unit_r : ∀ ε, ∃ ε', EA.comp ε EA.unit = some ε' ∧ EA.eqv ε' ε
  unit_l : ∀ ε, ∃ ε', EA.comp EA.unit ε = some ε' ∧ EA.eqv ε' ε
  assoc  : ∀ ε₁ ε₂ ε₃,
    ((∃ x y, EA.comp ε₁ ε₂ = some x ∧ EA.comp x ε₃ = some y) ∨
     (∃ x y, EA.comp ε₂ ε₃ = some x ∧ EA.comp ε₁ x = some y)) →
    ∃ x y x' y', EA.comp ε₁ ε₂ = some x ∧ EA.comp x ε₃ = some y ∧
      EA.comp ε₂ ε₃ = some x' ∧ EA.comp ε₁ x' = some y' ∧ EA.eqv y y'
  -- third bullet: substitution respecting well-formedness is a homomorphism for `⊙`, `(−)↑`, `∼`
  subst_comp : ∀ α S ε₁ ε₂ ε, EA.SubstOK α S [ε₁, ε₂] → EA.comp ε₁ ε₂ = some ε →
    EA.comp (EA.subst α S ε₁) (EA.subst α S ε₂) = some (EA.subst α S ε)
  subst_lift : ∀ α S L, (∃ Γ₁ Γ₂, EA.WFLab (Γ₁ ++ α :: Γ₂) L ∧ EA.WF Γ₁ S) →
    EA.subst α S (EA.lift L) = EA.lift L
  subst_eqv : ∀ α S ε₁ ε₂, EA.SubstOK α S [ε₁, ε₂] → EA.eqv ε₁ ε₂ →
    EA.eqv (EA.subst α S ε₁) (EA.subst α S ε₂)

/-- `ε₁ < ε₂`: "`ε₁ ⊙ ε ∼ ε₂` for some `ε`". -/
def EffAlg.Sub (EA : EffAlg) (ε₁ ε₂ : EA.Eff) : Prop :=
  ∃ ε x, EA.comp ε₁ ε = some x ∧ EA.eqv x ε₂

/-- A row with an optional tail variable (Rémy): a closed first-match prefix `ops`, then the row
the variable `tail` stands for. -/
structure ORow where
  ops  : Row
  tail : Option RVar

open Classical in
/-- **The minimal open-row form**: `⊙` is defined when the left row has no tail, or the right row
is empty, as for Yoshioka's simple rows; `∼` is equal tails and equal first-match lookup, so a
duplicate entry is shadowed as `Row.find` shadows it.  Reducible, so that its carrier is `ORow` to
every tactic. -/
@[reducible] def orowAlg (Ξ : EffCtx) : EffAlg where
  Lab := {n : UInt32 // n ≠ 0 ∧ Ξ n ≠ [] ∧ (Ξ n).length ≤ 2 ^ 32}
  Eff := ORow
  Var := RVar
  WF Γ ε := (∀ ρ, ε.tail = some ρ → ρ ∈ Γ) ∧
    ∀ n i o, Row.find ε.ops n i = some o → n ≠ 0 ∧ (Ξ n)[i.toNat]? = some (o.q, o.A, o.B)
  WFLab _ _ := True
  comp ε₁ ε₂ := match ε₁.tail with
    | none => some ⟨ε₁.ops ++ ε₂.ops, ε₂.tail⟩
    | some _ => if ε₂.ops = [] ∧ ε₂.tail = none then some ε₁ else none
  unit := ⟨[], none⟩
  lift n := ⟨Row.ofEff n.1 (Ξ n.1) 0, none⟩
  eqv ε₁ ε₂ := ε₁.tail = ε₂.tail ∧ RowEq ε₁.ops ε₂.ops
  subst ρ S ε := if ε.tail = some ρ then ⟨ε.ops ++ S.ops, S.tail⟩ else ε

/-- The closed rows: the sub-algebra with no row variable.  Reducible, as `orowAlg`. -/
@[reducible] def closedRowAlg (Ξ : EffCtx) : EffAlg where
  Lab := {n : UInt32 // n ≠ 0 ∧ Ξ n ≠ [] ∧ (Ξ n).length ≤ 2 ^ 32}
  Eff := Row
  Var := Empty
  WF _ S := ∀ n i o, Row.find S n i = some o → n ≠ 0 ∧ (Ξ n)[i.toNat]? = some (o.q, o.A, o.B)
  WFLab _ _ := True
  comp S S' := some (S ++ S')
  unit := []
  lift n := Row.ofEff n.1 (Ξ n.1) 0
  eqv := RowEq
  subst α _ _ := α.elim

/-- A row form: an effect algebra at each effect context, its labels' names, and its reading of an
effect, at an environment of its variables, as a closed row. -/
structure RowForm where
  alg  : EffCtx → EffAlg
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

/-! ### D4. Suspension: the frozen finalisers and the cancel branch -/

/-- The finalisers of `K`'s `[then]` frames (`ubind (N, D)`), innermost first.  In `.appR f K` the
frame `f` is outside `K`. -/
def _root_.BoCa.BoLo.Kont.fins : Kont → List Expr
  | .hole => []
  | .appR f K => K.fins ++ (match f with
      | .app (.prim .ubind) (.pair _ D) => [D]
      | _ => [])
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.fins

/-- The cancel branch of `κ = kappa n H K` after its three administrative steps. -/
def cancelOf (n : UInt32) (H : Val) (K : Kont) : Expr :=
  ccatchE (hndE H (K.plug (raiseE (.val (cancelVal (n :: K.hndNames) none)))))

end Targets

end
