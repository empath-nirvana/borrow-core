import Core.Fundamental
import Targets.Base.Rows

/-!
# System B — the borrow world (RESTRUCTURE §2.1)

**A borrow world** `BWorld` is BoLo's Kripke world `W = (ρ, ls, σ)` as a parameter, with borrow
fields only: the configurations it reaches (`Fam`), the run-end relation `↭` (`Upd`, a field,
FIX-RUN-END), the Kripke order (`Ext`), the payload stack (`payStk`, OQ-46) and the relation
(`val`, `comp`).  `coreB` is Core's relation as a borrow world whose lend stack has one point.

Everything here reads only these fields: the cell predicates at W (`ptoMutSW`, `ptoImmSW`), the
context relation (`gSepW`, `gDenW`) and the semantic judgement (`SemWC`, `SemW₀`, `SemW`); and the
transports to Core at `coreB` (`ptoMutSW_core`, `gDenW_core`, `semW₀_core`, …).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The index of `W = (ρ, ls, σ)`: the record list and the lend stack.  The resource `ρ` is the
argument of every `WProp`. -/
abbrev Idx (Stk : Type) := List SRec × Stk


end Targets

namespace Targets.B
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **A borrow world**: BoLo's Kripke world as a parameter.  It has the lend stack `σ`; the
configurations the world reaches (`TW` at Core); the run-end relation `↭`, a field
(FIX-RUN-END); the Kripke order; the stack a cell's stored payload is read at (OQ-46); and the
relation.  It has nothing of effects: no stop condition, no continuation share, nothing held by
suspensions.  `SemWorld` (`Targets/I/World.lean`) extends it with those. -/
structure BWorld where
  /-- σ.  What a lend stack holds is OQ-44's question; here it is a type. -/
  Stk    : Type
  nil    : Stk
  /-- The configurations the world reaches at an index: the full resource and the open 6.64
  frames visible to the running computation. -/
  Fam    : WRes → List FrameRec → Idx Stk → Prop
  /-- The run-end relation: a run from the resource `ρ` at the index `i` may end at the index `i′`
  with `π = ρ′ ● ρ⁺`, its postcondition holding `ρ′`.  Core's is `↭` ([TR] p. 5 row 18,
  `ResU.UpdV ρ π`), which reads neither index nor `ρ′`.  On the nil slice it is Core's
  (`SliceShapeB`).  Whether, and how, a run may end holding a lend it opened is OQ-9's question. -/
  Upd    : Idx Stk → Idx Stk → WRes → WRes → WRes → Prop
  /-- The Kripke order on indices, relative to a resource (Core's `Ext`). -/
  Ext    : Idx Stk → Idx Stk → WRes → Prop
  /-- The lend stack at which a cell at lifetime `b` reads its stored payload, given the stack of
  the index the cell is read at (OQ-46). -/
  payStk : Life → Stk → Stk
  /-- The relation, mode-indexed as `vCE` is. -/
  val    : Bool → VTy → Idx Stk → LSub → Val → WProp
  comp   : CTy → Idx Stk → LSub → Expr → WProp

/-- **Core's relation as a borrow world**, its lend stack one point.  Reducible, so that its index
type is `Idx Unit` to every tactic. -/
@[reducible] def coreB : BWorld where
  Stk := Unit
  nil := ()
  Fam fρ ps i := TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1
  Upd _ _ ρ _ π := ResU.UpdV ρ π
  Ext i i' ρ := Ext i.1 i'.1 ρ
  payStk _ _ := ()
  val b A i δ v := vCE none b A i.1 δ v
  comp C i δ e := cC (ℍ := ℍ) C i.1 δ e



end Targets.B

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `ℓ ↦ M_α P` at W: `ptoMutS` with the stored predicate read at the index
`(ls₀, M.payStk b i.2)`, `ls₀` the records of `i.1` strictly longer-lived than the cell. -/
def ptoMutSW (M : B.BWorld) (l : Loc) (α : Life) (i : Idx M.Stk) (P : Idx M.Stk → Val → WProp) :
    WProp := fun ρ =>
  ∃ (b : Life) (u : Val) (σ : WRes) (h : σ.InStratum b) (Q : Val → SPropS Loc Val b)
    (hw : Q u ⟨σ, h⟩) (ls₀ : List SRec),
    α ⊑ b ∧ ρ = ResU.single l (CellU.mutOf b u σ h Q hw) ∧ ofS Q = P (ls₀, M.payStk b i.2) ∧
    (∀ x, x ∈ ls₀ ↔ (x ∈ i.1 ∧ x.2 ⊐ b)) ∧ ∀ i' u' σ', P i' u' σ' → σ'.InStratum b

/-- `ℓ ↦ I_α P` at W: `ptoImmS` the same way, at the cell's `⊓β̄`. -/
def ptoImmSW (M : B.BWorld) (l : Loc) (α : Life) (i : Idx M.Stk) (P : Idx M.Stk → Val → WProp) :
    WProp := fun ρ =>
  ∃ (s : LSet) (u : Val) (σ : WRes) (h : σ.InStratum s.join) (ls₀ : List SRec),
    ρ = ResU.single l (CellU.immOf s u σ h) ∧ P (ls₀, M.payStk s.meet i.2) u σ ∧ α ⊑ s.meet ∧
    ∀ x, x ∈ ls₀ ↔ (x ∈ i.1 ∧ x.2 ⊐ s.meet)

/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧` at W (`gSepC`). -/
def gSepW (M : B.BWorld) (i : Idx M.Stk) (δ : LSub) : Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ => if s.live then M.val true s.ty i δ v ⋆ gSepW M i δ Γ γ else gSepW M i δ Γ γ

/-- `𝒢⟦Γ⟧` at W (`gDenC`). -/
def gDenW (M : B.BWorld) (i : Idx M.Stk) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepW M i δ Γ γ

/-- `Δ; Γ ⊨ e : C` at W at closed rows (`SemC`), at every index. -/
def SemWC (M : B.BWorld) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) : Prop :=
  ∀ δ γ (i : Idx M.Stk) ρ, Δ.Models δ → gDenW M i δ Γ γ ρ → M.comp C i δ (substAll γ e) ρ

/-- `Δ; Γ ⊨ e : j` at W at closed rows (`SemJ`): a value judgment is `return V` at `F A`. -/
def SemW₀ (M : B.BWorld) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) : Jdg → Prop
  | .comp C => SemWC M Δ Γ e C
  | .val A => SemWC M Δ Γ e (.ret A)

/-- At a row context: every admissible instance. -/
def SemW (M : B.BWorld) (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr)
    (j : RowEnv → Jdg) : Prop :=
  ∀ η, Θ.Models η → SemW₀ M Δ (Γ η) e (j η)


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- An index of `B.coreB` is a record list. -/
theorem idx_unit (i : Idx Unit) : i = (i.1, ()) := by rcases i with ⟨a, ⟨⟩⟩; rfl

/-- `ptoMutSW` at `B.coreB` is `ptoMutS`. -/
theorem ptoMutSW_core (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) :
    ptoMutSW (B.coreB (ℍ := ℍ)) l α (ls, ()) (fun i => P i.1) = ptoMutS l α ls P := by
  funext ρ
  apply propext
  constructor
  · rintro ⟨b, u, σ, h, Q, hw, ls₀, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨b, u, σ, h, Q, hw, ls₀, h₁, h₂, h₃, h₄, fun ls' => h₅ (ls', ())⟩
  · rintro ⟨b, u, σ, h, Q, hw, ls₀, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨b, u, σ, h, Q, hw, ls₀, h₁, h₂, h₃, h₄, fun i' => h₅ i'.1⟩

/-- `ptoImmSW` at `B.coreB` is `ptoImmS`. -/
theorem ptoImmSW_core (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) :
    ptoImmSW (B.coreB (ℍ := ℍ)) l α (ls, ()) (fun i => P i.1) = ptoImmS l α ls P := rfl

/-- `gSepW` at `B.coreB` is `gSepC`. -/
theorem gSepW_core (ls : List SRec) (δ : LSub) : ∀ (Γ : Ctx VTy) (γ : List Val),
    gSepW (B.coreB (ℍ := ℍ)) (ls, ()) δ Γ γ = gSepC (ℍ := ℍ) ls δ Γ γ
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: Γ, v :: γ => by
      simp only [gSepW, gSepC, gSepW_core ls δ Γ γ]

/-- `gDenW` at `B.coreB` is `gDenC`. -/
theorem gDenW_core (ls : List SRec) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) :
    gDenW (B.coreB (ℍ := ℍ)) (ls, ()) δ Γ γ = gDenC (ℍ := ℍ) ls δ Γ γ := by
  simp only [gDenW, gDenC]
  rw [gSepW_core]

/-- `SemWC` at `B.coreB` is `SemC`. -/
theorem semWC_core {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} :
    SemWC (B.coreB (ℍ := ℍ)) Δ Γ e C ↔ SemC (ℍ := ℍ) Δ Γ e C := by
  constructor
  · intro h δ γ ls ρ hδ hg
    exact h δ γ (ls, ()) ρ hδ (by rw [gDenW_core]; exact hg)
  · intro h δ γ i ρ hδ hg
    rcases i with ⟨ls, ⟨⟩⟩
    rw [gDenW_core] at hg
    exact h δ γ ls ρ hδ hg

/-- `SemW₀` at `B.coreB` is `SemJ`. -/
theorem semW₀_core {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} :
    ∀ {j : Jdg}, SemW₀ (B.coreB (ℍ := ℍ)) Δ Γ e j ↔ SemJ (ℍ := ℍ) Δ Γ e j
  | .comp _ => semWC_core
  | .val _ => semWC_core

theorem ptoMutSW_core_eq (l : Loc) (α : Life) (i : Idx (B.coreB (ℍ := ℍ)).Stk) (A : VTy) (δ : LSub) :
    ptoMutSW (B.coreB (ℍ := ℍ)) l α i (fun i₀ => vCE (ℍ := ℍ) none true A i₀.1 δ) =
      ptoMutS l α i.1 (fun ls₀ => vCE (ℍ := ℍ) none true A ls₀ δ) := by
  rcases i with ⟨ls, ⟨⟩⟩
  exact ptoMutSW_core l α ls (fun ls₀ => vCE none true A ls₀ δ)

end Targets

end
