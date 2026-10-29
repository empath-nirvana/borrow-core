import Core.EffBoxed

/-!
# SuspSpike — the class tables

A **grade** marks operations as call-like: a property of the operation `(n, i)`, read by the
protocol table. At a call-like stop the continuation is owed only at lists with the stop's
members (`contShareC`): the resumption happens in the scope where the operation was performed,
as a call returns there. Every other operation keeps Core's `contShare`.

`opTableC T C` is `opTable T` with that one change at the operations `C` marks. At the empty
grade it is `opTable T` (`Conservative.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace SuspSpike
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `ls'` has the members of `ls`: the convention of `wpG`'s last conjunct. -/
def SameMem (ls ls' : List SRec) : Prop := ∀ x, x ∈ ls' ↔ x ∈ ls

theorem SameMem.refl (ls : List SRec) : SameMem ls ls := fun _ => Iff.rfl

theorem SameMem.symm {ls ls' : List SRec} (h : SameMem ls ls') : SameMem ls' ls :=
  fun x => (h x).symm

theorem SameMem.trans {ls ls' ls'' : List SRec} (h₁ : SameMem ls ls') (h₂ : SameMem ls' ls'') :
    SameMem ls ls'' := fun x => (h₂ x).trans (h₁ x)

/-- A grade: the operations it marks are call-like. -/
abbrev Grade := UInt32 → UInt32 → Bool

/-- The empty grade. -/
def Grade.none : Grade := fun _ _ => false

/-- The continuation's share at a call-like stop: resumed at every list with the stop's members,
at every answer. It has no cancel: a call-like operation is linear. -/
def contShareC (en : OpEnt) (ls : List SRec) (K : Kont) (Φ : List SRec → Expr → WProp) : WProp :=
  fun ρ => ∀ ls', SameMem ls ls' → ∀ w : Val, (en.PB ls' w ─⋆ Φ ls' (K.plug (.val w))) ρ

/-- The share a graded table asks at the stop of `(n, i)`. -/
def shareAt (C : Grade) (n i : UInt32) (en : OpEnt) (ls : List SRec) (K : Kont)
    (Φ : List SRec → Expr → WProp) : WProp :=
  cond (C n i) (contShareC en ls K Φ) (contShare en ls K Φ)

theorem shareAt_true {C : Grade} {n i : UInt32} (h : C n i = true) (en : OpEnt) (ls : List SRec)
    (K : Kont) (Φ : List SRec → Expr → WProp) :
    shareAt C n i en ls K Φ = contShareC en ls K Φ := by
  unfold shareAt; rw [h]; rfl

theorem shareAt_false {C : Grade} {n i : UInt32} (h : C n i = false) (en : OpEnt) (ls : List SRec)
    (K : Kont) (Φ : List SRec → Expr → WProp) :
    shareAt C n i en ls K Φ = contShare en ls K Φ := by
  unfold shareAt; rw [h]; rfl

/-- A stop at a non-abortive operation, its share by the grade. -/
def performStopC (T : OpTab) (C : Grade) : Table := fun ls t Φ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEnt) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false⌝ ⋆ (en.PA ls v ⋆ shareAt C n i en ls K Φ)

/-- The graded protocol table: `opTable T` with `contShareC` at the call-like operations. -/
def opTableC (T : OpTab) (C : Grade) : Table := fun ls t Φ =>
  BoLo.or (performStopC T C ls t Φ)
    (ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
      ex fun (en : OpEnt) =>
        ⌜t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
          T n i = some en ∧ en.abort = true⌝ ⋆
          ((fun ρ => en.PA ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ))

/-- **Class 1**, at an operation table: every operation is call-like, linear and resumes, and
its answers lie in every stratum (closed data, as `Row.ResumeO` asks). -/
def CallRow (T : OpTab) (C : Grade) : Prop :=
  (∀ n i en, T n i = some en → C n i = true ∧ en.q = .lin ∧ en.abort = false) ∧
    ∀ α, OpTab.AnsIn α T

/-- A table owes continuations only at lists with the stop's members. -/
def Table.Scoped (Tb : Table) : Prop :=
  ∀ ls t (Φ Φ' : List SRec → Expr → WProp) ρ,
    (∀ ls' e ρ, SameMem ls ls' → Φ ls' e ρ → Φ' ls' e ρ) → Tb ls t Φ ρ → Tb ls t Φ' ρ

end SuspSpike

end
