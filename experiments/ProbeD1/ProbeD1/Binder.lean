import ProbeD1.Relendability
import Targets.I.Binder

/-!
# ProbeD1 — the freeze binder at W: PlaceViews and the lifetime instantiation (`BINDER.md`)

"Freeze is a binder over internal locations, lifetimes and instances; resume and placement
instantiate it" (user, 2026-10-04). This file states the binder's location reading (a place the
stack lends is a bound location, and a value there is the binder's view) and its lifetime half (the
re-lend at a resume is an order-preserving instantiation of every internal lifetime). `BINDER.md` is
the design; its §5 gives the revision of W's clauses these definitions enter.

* **PlaceViews.**
  - `PlaceViewsW`: the invariant read off a configuration's world. At a place whose innermost lending
    entry is a 6.65 entry, the world's `mut` cell is at the entry's current lifetime and stores
    `𝒱⟦T⟧` of the entry's payload type; at a 6.64 entry's place, the world's `imm` cell is at the
    entry's lifetime and holds the entry's value. Its preservation along `Arises` is `PVArises`.
  - `PlaceViewsAt`: W's guard conjunct. Every top-level borrow cell of the local resource at a stack
    place is the innermost entry's view at the stack's reading, at the entry's exact lifetime.
  - `CohS`: W's `Mut` and `Imm` leaves at a stack place. The view's payload type is the entry's up
    to the reading (`TyEq`), and its cell is at the entry's lifetime. It is the 6.65 analog of
    Core's `CohE`, which ties an `imm` cell to its 6.64 record.
  - `vwEW`, `vwSW`: W's views. GhostEnd's, read at the stack's reading, the cell at the exact
    lifetime.
* **The instantiation.** `Inst` is the identity or a re-stratification `Restrat.Emb c` at the
  stack's cut `cutOf αs`, the lifetime just above the outermost lend. It moves every lifetime below
  the cut, strictly monotonically and downward, and fixes every one at or above it. It acts on the
  index: the reading substitution (`Inst.sub`), the lend lifetimes (`Inst.life`), and the record
  list's substitutions and frame lifetimes (`Inst.recs`). It transports no resource: the part a `U`
  value retains lies above the cut, and the views are handed afresh.
  - `RelendI` (the stack itself) and `RelendUI` (its futures): W's `U` clause over instantiations.
  - `InstModels`: an instantiation keeps every lifetime context's models. It replaces
    `BoundsStackFree`.
  - `InternalVar` (semantic) and `BoundBelowV` (the bound reaches below a stack variable), with
    `InternalOfBound` between them.
  - `InstFresh`, `InstFreshExists`: a resume's instantiation, fresh beneath the resumer's resource
    ([TR] 6.112).
  - The equivariance the thaw needs: `TyEqInst`, `MutPayloadInst`, `InstEquivLeaf` (at types Core
    reads without a thunk, `CoreStable`), `ViewSlotInst`; and why the leaf must tie the type,
    `ViewTypeCoincidence`.
* **The known risk.** `Targets.NotVDenNaturalArises` (the TW history), `InternalPayloadArises`
  (the witness's shape with both lends on W's stack), and, beside them, `NotVCNaturalCore`
  (transport, as `FreezeBinderLife` states it, fails at Core's relation).
* **The `U` introductions retried.** `CtxRelendableAtI`, `ThawFree`, `ThawInst`, and the four rows
  at slot types the thaw handles (`ThunkFRowTF` and its siblings).

Definitions and `def … : Prop` statements only; no proofs. The statements over `vRL`, `gRL` and
`SemS` are read at W as `BINDER.md` §5 revises it.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)

/-! ### Bound places -/

/-- The innermost entry lending the place `l`, with its current lifetime. -/
def innerAt (σ : LStack) (αs : List Life) (l : BoCa.Loc) : Option (LEnt × Life) :=
  (σ.zip αs).find? fun p => decide (p.1.l = l)

/-- **PlaceViews at a configuration**, read off the world's flattening. At a place whose innermost
lending entry is a 6.65 entry, the world's `mut` cell there is at the entry's current lifetime and
stores `𝒱⟦T⟧` of the entry's payload type, at some reading and list. At a 6.64 entry's place, the
world's `imm` cell there is at the entry's current lifetime and holds the entry's value. -/
def PlaceViewsW (σ : LStack) (αs : List Life) (fρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (e : LEnt) (α : Life), innerAt σ αs l = some (e, α) →
    ∀ ψ : CellU BoCa.Loc Val, fρ.FlatAt l ψ →
      (e.k = .mut → ψ.kind = Kind.mut → ψ.at = α ∧
        ∃ (δ' : LSub) (ls₀ : List SRec), mutPred ψ = fun v => vC true e.T ls₀ δ' v) ∧
      (∀ u, e.k = .imm u → ψ.kind = Kind.imm → ψ.at = α ∧ ψ.erase = u)

/-- **W's view of one entry**: GhostEnd's view read at the reading `s` (the stack's), its cell at
exactly the entry's lifetime `α`. -/
def vwEW (s : LSub) (e : LEnt) (d : Bool) (α : Life) (ls : List SRec) : WProp := fun ρ =>
  vwE s e d α ls ρ ∧ ∀ ψ, ρ.get e.l = some ψ → ψ.at = α

/-- **W's views of a stack**, an entry whose place an inner entry lends again shadowed, as `vwS`. -/
def vwSW (s : LSub) : List BoCa.Loc → LStack → List Bool → List Life → List SRec → WProp
  | _, [], [], [], _ => emp
  | seen, e :: σ, d :: ds, α :: αs, ls =>
      vwEW s e (vis seen e d) α ls ⋆ vwSW s (e.l :: seen) σ ds αs ls
  | _, _, _, _, _ => fun _ => False

/-- **W's guard conjunct**: every top-level borrow cell of `ρ` at a place the stack lends is the
innermost lending entry's view at the reading `s`, at the entry's current lifetime. -/
def PlaceViewsAt (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (ρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val), ρ.get l = some ψ → ψ.kind ≠ Kind.own →
    ∀ (e : LEnt) (α : Life), innerAt σ αs l = some (e, α) → vwEW s e true α ls (ResU.single l ψ)

/-- **W's guard, revised**: the stack's table and its views. It replaces `guardW` (`BINDER.md`
§5.1). -/
def guardPV (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (P : WProp) : WProp :=
  fun ρ => TabAtS σ αs ρ → PlaceViewsAt s σ αs ls ρ → P ρ

/-- A view type's kind and payload against the entry lending its place: a `Mut` view at a 6.65
entry, an `Imm` view at a 6.64 entry, the payload types one type up to the reading. -/
def CohKind (s : LSub) (e : LEnt) : VTy → Prop
  | .mut _ T => (match e.k with | .mut => True | .imm _ => False) ∧ TyEq T s e.T s
  | .imm _ T => (match e.k with | .mut => False | .imm _ => True) ∧ TyEq T s e.T s
  | _ => False

/-- **A view at a bound place is the binder's view.** W's `Mut` and `Imm` leaves at a place the
stack lends: the innermost lending entry is of the view's kind, its payload type is the view's up
to the reading, and the view's cell is at the entry's current lifetime. The 6.65 analog of Core's
`CohE`. -/
def CohS (σ : LStack) (αs : List Life) (s : LSub) (A : VTy) (v : Val) (ρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (e : LEnt) (α : Life), v = .loc l → innerAt σ αs l = some (e, α) →
    CohKind s e A ∧ ∀ ψ, ρ.get l = some ψ → ψ.at = α

/-! ### The instantiation -/

/-- **An instantiation**: the identity (`none`), or a re-stratification at a cut. -/
abbrev Inst := Option (Σ c : Life, Restrat.Emb c)

namespace Inst

/-- On one lifetime. -/
def life1 : Inst → Life → Life
  | none => fun a => a
  | some ⟨_, θ⟩ => θ

/-- On the lend lifetimes. -/
def life (ι : Inst) (αs : List Life) : List Life := αs.map ι.life1

/-- On a substitution: `θ ∘ δ`. -/
def sub : Inst → LSub → LSub
  | none => fun δ => δ
  | some ⟨_, θ⟩ => Restrat.LSub.mapN θ.toNat

/-- On the record list: each record's substitution and frame lifetime. Its witness is kept, since no
resource is transported. -/
def recs (ι : Inst) (ls : List SRec) : List SRec :=
  ls.map fun x => (⟨x.1.le, x.1.v, x.1.R, x.1.T, ι.sub x.1.δ⟩, ι.life1 x.2)

/-- The instantiation a re-stratification gives. -/
def ofEmb {c : Life} (θ : Restrat.Emb c) : Inst := some ⟨c, θ⟩

end Inst

/-- **The cut of a stack**: the lifetime just above its outermost lend. The empty stack has none,
and nothing is internal there. -/
def cutOf (αs : List Life) : Option Life :=
  αs.getLast?.map fun o => OrderDual.toDual (OrderDual.ofDual o - 1)

/-- **The stack's instantiations**: the identity, or a re-stratification at the stack's cut. -/
def InstAt (αs : List Life) (ι : Inst) : Prop :=
  ∀ (c : Life) (θ : Restrat.Emb c), ι = some ⟨c, θ⟩ → cutOf αs = some c

/-- **W's `U` clause over instantiations, at the stack itself** (`binder0`). The resource splits into
the views it holds and a part strictly above the outermost lend. At every instantiation of the
stack's internal lifetimes, every extension of the instantiated list, handed the views at the
instantiated stack, that part is in `P` at the instantiated reading. -/
def RelendI (δ : LSub) (σ : LStack) (P : LSub → List Life → List SRec → WProp)
    (αs : List Life) (ls : List SRec) : WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwSW (extS δ σ αs) [] σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ ι, InstAt αs ι → ∀ ls', Ext (ι.recs ls) ls' ρz →
      (vwSW (extS (ι.sub δ) σ (ι.life αs)) [] σ ds (ι.life αs) ls' ─⋆
        P (ι.sub δ) (ι.life αs) ls') ρz

/-- **W's `U` clause over instantiations and futures** (`cbpv`, `binder`): `RelendU` with the
re-lend replaced by an instantiation. -/
def RelendUI (fut own : Bool) (δ : LSub) (σ : LStack) (C : CTy)
    (P : LStack → LSub → List Life → List SRec → WProp) (αs : List Life) (ls : List SRec) :
    WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwSW (extS δ σ αs) [] σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ ι, InstAt αs ι → ∀ ls', Ext (ι.recs ls) ls' ρz →
      ∀ σ' αs'', FutQ fut (ι.sub δ) ρz (σ, ι.life αs) (σ', αs'') → FutAvoids C σ σ' →
        (vwSW (extS (ι.sub δ) σ (ι.life αs)) [] σ ds (ι.life αs) ls' ─⋆
          P σ' (ι.sub δ) αs'' ls') ρz ∧
        (own = true → ∀ (e : LEnt) (a : Life), OwnPush (ι.sub δ) C ρz (σ', αs'') e a →
          (vwSW (extS (ι.sub δ) σ (ι.life αs)) [] σ ds (ι.life αs) ls' ─⋆
            P (e :: σ') (ι.sub δ) (a :: αs'') ls') ρz)

/-! ### Internal lifetimes -/

/-- **An internal lifetime** of a stack: at or below its outermost lend. -/
def Internal (αs : List Life) (a : Life) : Prop := ∃ o ∈ αs.getLast?, a ≤ o

/-- **An internal variable** of an index: one the stack's reading sends to an internal lifetime. An
instantiation at the stack's cut moves exactly the values of these. -/
def InternalVar (δ : LSub) (σ : LStack) (αs : List Life) (y : LifeVar) : Prop :=
  ∃ m, (extS δ σ αs).find? y = some m ∧ Internal αs (OrderDual.toDual m)

mutual
/-- **A variable whose bound reaches below the stack**: a stack variable, or a variable of `Δ` off
the stack whose bound does. -/
inductive BoundBelowV (Δ : LifeCtx) (σ : LStack) : LifeVar → Prop
  | stack {y : LifeVar} : y ∈ σ.map LEnt.x → BoundBelowV Δ σ y
  | bound {y : LifeVar} {u : Lifetime.Life} : y ∉ σ.map LEnt.x → Δ.find? y = some u →
      BoundBelowL Δ σ u → BoundBelowV Δ σ y
/-- A bound that reaches below the stack: a variable that does, a meet with one operand that does
(`⊓` is the shorter), a join with both that do (`⊔` is the longer). -/
inductive BoundBelowL (Δ : LifeCtx) (σ : LStack) : Lifetime.Life → Prop
  | var {z : LifeVar} : BoundBelowV Δ σ z → BoundBelowL Δ σ (.var z)
  | meetL {a b : Lifetime.Life} : BoundBelowL Δ σ a → BoundBelowL Δ σ (.meet a b)
  | meetR {a b : Lifetime.Life} : BoundBelowL Δ σ b → BoundBelowL Δ σ (.meet a b)
  | join {a b : Lifetime.Life} : BoundBelowL Δ σ a → BoundBelowL Δ σ b →
      BoundBelowL Δ σ (.join a b)
end

/-- **The syntactic description is inside the semantic one**: at an index that models `Δ`, a
variable whose bound reaches below the stack is internal. The converse does not hold, and the
instantiation moves the other internal variables too, which keeps `Δ`'s models (`InstModels`). -/
def InternalOfBound : Prop :=
  ∀ (Δ : LifeCtx) (δ : LSub) (σ : LStack) (αs : List Life) (y : LifeVar),
    StackOK σ αs → Δ.Models (extS δ σ αs) → BoundBelowV Δ σ y → InternalVar δ σ αs y

/-! ### The models at an instantiation (replacing `BoundsStackFree`) -/

/-- **An instantiation keeps every lifetime context's models**: `extS` commutes with `θ ∘ -`, and
`⟦Δ⟧` is invariant under a re-stratification (`Restrat.Emb.models_mapN_iff`). No condition on `Δ`'s
bounds. -/
def InstModels : Prop :=
  ∀ (Δ : LifeCtx) (δ : LSub) (σ : LStack) (αs : List Life) (ι : Inst),
    Δ.Models (extS δ σ αs) → Δ.Models (extS (ι.sub δ) σ (ι.life αs))

/-- **`ReLendModels` at the instantiations**: every instantiation of the stack models `Δ`. It is what
the `U` rows ask at `RelendI`, and it follows from `InstModels`. -/
def ReLendModelsI (Δ : LifeCtx) (δ : LSub) (σ : LStack) (αs : List Life) : Prop :=
  ∀ ι, InstAt αs ι → Δ.Models (extS (ι.sub δ) σ (ι.life αs))

/-- **`q2_reached`'s configuration is kept by every instantiation**: lowering `'0` lowers `'1 ⊏ '0`
with it. -/
def Q2Inst : Prop := ReLendModelsI mΔ qδ [qEnt] [kα]

/-! ### Freshness at a resume ([TR] 6.108–6.112) -/

/-- **A fresh instantiation**: every lifetime it moves lands strictly below every cell of the
resumer's resource `R` ([TR] 6.112's `И`, at a block of lifetimes). -/
def InstFresh (R : WRes) : Inst → Prop
  | none => True
  | some ⟨c, θ⟩ => ∀ a, a < c → R.InStratum (θ a)

/-- **Fresh instantiations exist** at every stack with a cut and every resumer's resource
(`Restrat.Emb.shift_fresh`). -/
def InstFreshExists : Prop :=
  ∀ (αs : List Life) (R : WRes) (c : Life), cutOf αs = some c →
    ∃ θ : Restrat.Emb c, InstFresh R (Inst.ofEmb θ)

/-! ### Bookkeeping the rows read at an instantiation -/

/-- **An instantiation of a stack in shape is a re-lend of it** (`ReLend`): it lowers each lend
lifetime and keeps their nesting order. -/
def InstReLend : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ι : Inst), StackOK σ αs → InstAt αs ι → ReLend (ι.life αs) αs

/-- **The stack's reading commutes with an instantiation.** -/
def ExtSInst : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ι : Inst), αs.length = σ.length →
    extS (ι.sub δ) σ (ι.life αs) = ι.sub (extS δ σ αs)

/-- **Instantiations compose**: an instantiation of an instantiated stack, after the first, is an
instantiation of the stack (the second's cut is at or below the first's). -/
def InstComp : Prop :=
  ∀ (αs : List Life) (ι₁ ι₂ : Inst), InstAt αs ι₁ → InstAt (ι₁.life αs) ι₂ →
    ∃ ι : Inst, InstAt αs ι ∧ (∀ δ, ι.sub δ = ι₂.sub (ι₁.sub δ)) ∧
      (∀ a, ι.life1 a = ι₂.life1 (ι₁.life1 a)) ∧ ∀ ls, ι.recs ls = ι₂.recs (ι₁.recs ls)

/-- **An extension of the list is one of the instantiated lists**, at a resource above the stack's
outermost lend, which the instantiation fixes. -/
def ExtInst : Prop :=
  ∀ (ls ls' : List SRec) (ρ : WRes) (αs : List Life) (ι : Inst), InstAt αs ι → stratS αs ρ →
    Ext ls ls' ρ → Ext (ι.recs ls) (ι.recs ls') ρ

/-- **The stack's entries in a judgement are entries of it at an instantiation**: the own lend's
bound is read at the instantiated reading (`Restrat.Emb.ltLife_mapN_iff`). -/
def StackJInst : Prop :=
  ∀ (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (ι : Inst),
    αs.length = σ.length → StackJ σ αs δ Δ Γ C → StackJ σ (ι.life αs) (ι.sub δ) Δ Γ C

/-- **The table and the views at an instantiation**: a part above the outermost lend, handed W's
views at the instantiated stack, has the table and the guard's views there. -/
def GuardInst : Prop :=
  ∀ (δ : LSub) (σ : LStack) (ds : List Bool) (αs : List Life) (ls ls' : List SRec)
    (ρz ρn ρ ρv R : WRes) (ι : Inst),
    StackOK σ αs → InstAt αs ι → stratS αs ρz → vwSW (extS δ σ αs) [] σ ds αs ls ρn →
    ResU.CompS ρz ρn ρ → PlaceViewsAt (extS δ σ αs) σ αs ls ρ →
    vwSW (extS (ι.sub δ) σ (ι.life αs)) [] σ ds (ι.life αs) ls' ρv → ResU.CompS ρz ρv R →
    TabAtS σ (ι.life αs) R ∧ PlaceViewsAt (extS (ι.sub δ) σ (ι.life αs)) σ (ι.life αs) ls' R

/-- **A configuration that arises carries its frame, its local part and a valid world.** -/
def ArisesInv : Prop :=
  ∀ c : Cfg, Arises (ℍ := ℍ) c →
    ResU.Hash c.ρf c.ρ ∧ ResU.CompS c.ρf c.ρ c.fρ ∧ ResU.Valid c.fρ

/-! ### The equivariance the thaw needs -/

/-- **`TyEq` is kept by an instantiation of both readings.** -/
def TyEqInst : Prop :=
  ∀ (A B : VTy) (s s' : LSub) (ι : Inst), TyEq A s B s' → TyEq A (ι.sub s) B (ι.sub s')

/-- **A type Core's relation reads without a thunk**: no `U`, no `μ`, no array family. At such a type
Core's relation involves no `wp`, and every lifetime it reads is a lower bound on a cell. -/
def CoreStable : VTy → Prop
  | .thunk _ => False
  | .mu _ => False
  | .fam _ => False
  | .tensor A B => CoreStable A ∧ CoreStable B
  | .sum A B => CoreStable A ∧ CoreStable B
  | .bang A => CoreStable A
  | .box _ A => CoreStable A
  | .ref A => CoreStable A
  | .imm _ A => CoreStable A
  | .mut _ A => CoreStable A
  | _ => True

/-- **A slot type the thaw handles**: W's own formers down to `U`, which W instantiates by
construction, and leaves whose payloads Core reads without a thunk. `μ` and `fam` are handed to
Core's relation whole, and its `U` clause is not instantiated. -/
def ThawFree : VTy → Prop
  | .thunk _ => True
  | .tensor A B => ThawFree A ∧ ThawFree B
  | .sum A B => ThawFree A ∧ ThawFree B
  | .bang A => ThawFree A
  | .box _ A => ThawFree A
  | .ref A => ThawFree A
  | .mu _ => False
  | .fam _ => False
  | A => CoreStable A

/-- A context the thaw handles: every live slot's type is `ThawFree`. -/
def CtxThawFree (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → ThawFree s.ty

/-- **The guard sees cells, not types.** Two payload types can give one stored invariant at a reading
and different ones at an instantiation of it: a comparison against two adjacent internal lifetimes
agrees on `ℕ` and not after the instantiation spreads them. So a cell at a bound place being its
entry's view does not make a slot holding it typed as the entry's payload, and the leaf says so
(`CohS`), as Core's `CohE` does for an `imm` cell. -/
def ViewTypeCoincidence : Prop :=
  ∃ (T T' : VTy) (s : LSub) (ls : List SRec) (c : Life) (θ : Restrat.Emb c),
    (∀ u σ', vC true T ls s u σ' ↔ vC true T' ls s u σ') ∧
      ¬ ∀ u σ', vC true T (Inst.recs (Inst.ofEmb θ) ls) (Inst.sub (Inst.ofEmb θ) s) u σ' ↔
        vC true T' (Inst.recs (Inst.ofEmb θ) ls) (Inst.sub (Inst.ofEmb θ) s) u σ'

/-- **A supported `Mut` payload is fixed by an instantiation whose cut is at or below its stratum.**
This is the case of `mut_not_natural`'s shape that the instantiation meets: the cell is not moved,
and its stored invariant is re-read at the instantiated reading and list. -/
def MutPayloadInst : Prop :=
  ∀ (T : VTy) (ls₀ : List SRec) (s : LSub) (b c : Life) (θ : Restrat.Emb c), CoreStable T →
    c ≤ b → (∀ ls' u σ', vC true T ls' s u σ' → σ'.InStratum b) →
    ∀ u σ', vC true T (Inst.recs (Inst.ofEmb θ) ls₀) (Inst.sub (Inst.ofEmb θ) s) u σ' ↔
      vC true T ls₀ s u σ'

/-- **Core's relation is kept by an instantiation at a resource it fixes**: at a type read without a
thunk, at a resource all of whose cells are at or above the cut, it holds at the instantiated reading
and list. W's leaves off the stack's places, at the part a `U` value retains, are its instances. -/
def InstEquivLeaf : Prop :=
  ∀ (A : VTy) (b : Bool) (ls : List SRec) (s : LSub) (v : Val) (ρ : WRes) (c : Life)
    (θ : Restrat.Emb c), CoreStable A → StratumLe ρ c → vCE none b A ls s v ρ →
    vCE none b A (Inst.recs (Inst.ofEmb θ) ls) (Inst.sub (Inst.ofEmb θ) s) v ρ

/-- **A view slot is re-established from the view handed at the instantiation.** This is what the
instantiation asks in place of naturality. The slot's cell is not moved: it is dropped, and the view
handed at the instantiated reading re-establishes the slot by `TyEq` and the exact lifetime. The
stored invariant of the dropped cell is never read. -/
def ViewSlotInst : Prop :=
  ∀ (σ : LStack) (αs : List Life) (s : LSub) (ls ls' : List SRec) (A : VTy) (l : BoCa.Loc)
    (e : LEnt) (α : Life) (ρ ρv : WRes) (ι : Inst),
    innerAt σ αs l = some (e, α) → ι.recs ls ⊆ ls' →
    vC true A ls s (.loc l) ρ → CohS σ αs s A (.loc l) ρ →
    vwEW (ι.sub s) e true (ι.life1 α) ls' ρv →
    vC true A ls' (ι.sub s) (.loc l) ρv ∧ CohS σ (ι.life αs) (ι.sub s) A (.loc l) ρv

/-! ### PlaceViews along `Arises` -/

/-- At the empty stack there is no bound place. -/
def PVWNil : Prop := ∀ W : WRes, PlaceViewsW [] [] W

/-- **`↭` keeps PlaceViews**: its `mut` clause keeps a `mut` cell's lifetime and invariant at the
flattening, its `imm` clause keeps an `imm` cell. -/
def PVWUpd : Prop :=
  ∀ (σ : LStack) (αs : List Life) (W W' : WRes), PlaceViewsW σ αs W → ResU.UpdV W W' →
    PlaceViewsW σ αs W'

/-- **A run keeps PlaceViews**: [TR] 6.48 carries the run's `↭` on the local part to the world (the
frame `ρ_f`, the garbage joining it), and `PVWUpd` applies there. -/
def PVWRun : Prop :=
  ∀ (c c' : Cfg) (e t : Expr), ResU.Hash c.ρf c.ρ → ResU.CompS c.ρf c.ρ c.fρ →
    PlaceViewsW c.σ c.αs c.fρ → RunEnd (ℍ := ℍ) c e c' t → PlaceViewsW c'.σ c'.αs c'.fρ

/-- **A 6.65 lend opens with PlaceViews at its place** (`lendMut_placeView`, at the world), and keeps
it elsewhere. -/
def PVWLendMut : Prop :=
  ∀ (c c' : Cfg) (e : LEnt), ResU.Valid c.fρ → PlaceViewsW c.σ c.αs c.fρ → LendMut c c' e →
    PlaceViewsW c'.σ c'.αs c'.fρ

/-- **A 6.64 lend opens with PlaceViews at its place**, and keeps it elsewhere. -/
def PVWLendImm : Prop :=
  ∀ (c c' : Cfg) (e : LEnt), ResU.Valid c.fρ → PlaceViewsW c.σ c.αs c.fρ → LendImm c c' e →
    PlaceViewsW c'.σ c'.αs c'.fρ

/-- **A handler keeps PlaceViews**: it reads no entry's row. -/
def PVWHide : Prop :=
  ∀ (N : UInt32 → Bool) (σ : LStack) (αs : List Life) (W : WRes), PlaceViewsW σ αs W →
    PlaceViewsW (hideS N σ) αs W

/-- **PlaceViews holds at every configuration that arises.** -/
def PVArises : Prop := ∀ c : Cfg, Arises (ℍ := ℍ) c → PlaceViewsW c.σ c.αs c.fρ

/-- **The local part reads it**: a top-level `mut` cell of a part of a valid world is the world's
cell at its place (`ex` of the part is a `●`-factor of `ex` of the world, and a `mut` cell composes
with nothing). -/
def PVLocal : Prop :=
  ∀ (fρ ρf ρ : WRes), ResU.Valid fρ → ResU.CompS ρf ρ fρ →
    ∀ (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val), ρ.get l = some ψ → ψ.kind = Kind.mut →
      fρ.FlatAt l ψ

/-- **`k` does not arise**: no configuration that arises has `k`'s stack, lifetimes and local part. -/
def KNotArises : Prop :=
  ∀ c : Cfg, Arises (ℍ := ℍ) c → c.σ = kσ → c.αs = [kα] → c.ρ ≠ kρ

/-! ### The known risk: `mut_not_natural` -/

/-- **The shape of `mut_not_natural`'s witness arises at W**: a configuration with a 6.65 entry
whose payload type mentions the variable of a 6.64 entry outside it, both on the stack, so both
internal at the stack's cut. -/
def InternalPayloadArises : Prop :=
  ∃ c : Cfg, Arises (ℍ := ℍ) c ∧ ∃ (x b : LEnt) (u : Val), c.σ = [x, b] ∧ x.k = .mut ∧
    b.k = .imm u ∧ VFree b.x x.T

/-- **Beside: transport fails at Core's relation.** At the Core analog of `mut_not_natural`'s
witness, moving the resource with the reading and the records (`Restrat.Emb.relRU`, as
`Targets.FreezeBinderLife` does) loses the relation. The instantiation does not move it
(`ViewSlotInst`). -/
def NotVCNaturalCore : Prop :=
  ∃ (T : VTy) (s : LSub) (ls : List SRec) (v : Val) (ρ : WRes),
    vC true T ls s v ρ ∧
      ¬ vC true T (Inst.recs (Inst.ofEmb (Restrat.Emb.shift ⊤ 1)) ls)
        (Inst.sub (Inst.ofEmb (Restrat.Emb.shift ⊤ 1)) s) v ((Restrat.Emb.shift ⊤ 1).relRU ρ)

/-! ### The `U` introductions retried -/

/-- **The context's thaw over instantiations**, at one row's context: at every index `SemS` admits,
the guard's views included, a context related at the stack is re-lendable over instantiations. -/
def CtxRelendableAtI (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → SubDom δ Δ → Δ.Models (extS δ σ αs) → TabAtS σ αs ρ →
    PlaceViewsAt (extS δ σ αs) σ αs ls ρ → gRL p σ δ αs ls Γ γ ρ →
    RelendI δ σ (fun δ' αs' ls' => gRL p σ δ' αs' ls' Γ γ) αs ls ρ

/-- **The thaw at every context the thaw handles.** -/
def CtxRelendsThawFree (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy), CtxThawFree Γ → CtxRelendableAtI p Δ Γ

/-- **A `U` value instantiated is a `U` value at the instantiation** (`ThawRelend` over
instantiations). -/
def ThawInst (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec) (f : Val) (ρ : WRes),
    StackOK σ αs → TabAtS σ αs ρ → PlaceViewsAt (extS δ σ αs) σ αs ls ρ →
    vRL p σ δ (.thunk C) αs ls f ρ →
    RelendI δ σ (fun δ' αs' ls' => vRL p σ δ' (.thunk C) αs' ls' f) αs ls ρ

/-- **`thunk M : U (F A)`** at a context the thaw handles. -/
def ThunkFRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxThawFree Γ →
    SemS p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemS p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))

/-- **`thunk V : U C`** at a context the thaw handles. -/
def ThunkVRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxThawFree Γ → C.isRet = false →
    OwnHyg Δ Γ C → SemS p Δ Γ (.val (.lam N)) (.comp C) →
    SemS p Δ Γ (.val (.lam N)) (.val (.thunk C))

/-- **`!thunk M : !U (F A)`** at a persistent context the thaw handles. -/
def BangThunkFRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxThawFree Γ → Persistent Γ →
    SemS p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemS p Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))

/-- **`!thunk V : !U C`** at a persistent context the thaw handles. -/
def BangThunkVRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxThawFree Γ → Persistent Γ →
    C.isRet = false → OwnHyg Δ Γ C → SemS p Δ Γ (.val (.lam N)) (.comp C) →
    SemS p Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

/-- **The `U` side of statement 0 over instantiations**, at the contexts the thaw handles. -/
def Statement0U (p : Placement) : Prop :=
  ThawInst (ℍ := ℍ) p ∧ CtxRelendsThawFree (ℍ := ℍ) p ∧ ThunkFRowTF (ℍ := ℍ) p ∧
    ThunkVRowTF (ℍ := ℍ) p ∧ BangThunkFRowTF (ℍ := ℍ) p ∧ BangThunkVRowTF (ℍ := ℍ) p

end ProbeD1

end
