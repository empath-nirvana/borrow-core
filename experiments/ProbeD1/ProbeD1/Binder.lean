import ProbeD1.Relendability
import Targets.I.Binder

/-!
# ProbeD1 — the freeze binder at W: PlaceViews and the lifetime instantiation (`BINDER.md`)

Freeze is a binder over internal locations, lifetimes and instances; resume and placement
instantiate it. This file states the binder's location half (a place the stack lends is a bound
location, and a borrow cell there, at any depth, is the binder's view) and its lifetime half (the
re-lend at a resume is an order-preserving instantiation of every internal lifetime). `BINDER.md`
is the design; its §5 gives the revision of W's clauses these definitions enter.

* **PlaceViews.**
  - `PlaceViewsL`: W's guard conjunct. Every borrow cell of the local resource at a place the
    stack lends, at any depth (`DeepAt`), is a view of an entry lending that place, read at the
    stack's reading, its cell at the entry's exact lifetime; under no `imm` ancestor (`ExAt`), of
    the innermost such entry. Its top-level part is `PlaceViewsAt`, which the thaw reads. The local
    bundle `PVLBundle` states it as the stack's run invariant, one fact per transition and per
    configuration the relation quantifies over, the analog of statement 1's table facts.
  - `PlaceViewsW`: a shape of the same read off a configuration's world. Its preservation along
    `Arises` (`PVArises`) is the arising check that `k` does not arise (`KNotArises`). The guard
    does not rest on it.
  - `CohS`: W's `Mut` and `Imm` leaves at a stack place. The view's payload type is the entry's up
    to the reading (`TyEq`), and its cell is at the entry's lifetime. It is the 6.65 analog of
    Core's `CohE`, which ties an `imm` cell to its 6.64 record.
  - `vwEW`, `vwSW`: W's views, GhostEnd's read at the stack's reading, the cell at the exact
    lifetime; `vwSL` adds that their nested cells at the stack's places are views as well.
* **The instantiation.** `Inst` is the identity or a re-stratification `Restrat.Emb c` at the
  stack's cut `cutOf αs`. It moves the lifetimes below the cut, strictly monotonically and
  downward, and fixes every one at or above it. It acts on the index: the reading substitution
  (`Inst.sub`), the lend lifetimes (`Inst.life`), and the records whose frame lifetime is below the
  cut (`Inst.recs`); a record at or above the cut is left as it is. It transports no resource.
  - `RecsOutside`: every record outliving one of the stack's lends reads only lifetimes outliving
    it. An index invariant, from the lends' freshness (`LendFresh`); with it a record the
    instantiation leaves alone is coherent at the instantiated reading (`CohEInst`).
  - `RelendI` (the stack itself) and `RelendUI` (its futures): W's `U` clause over
    instantiations.
  - `InstModels`: an instantiation keeps every lifetime context's models.
  - `Internal`, `InternalVar` (semantic) and `BoundBelowV` (the bound reaches below a stack
    variable), with `InternalOfBound` between them.
  - `InstFresh`, `InstFreshExists`: a resume's instantiation, fresh below the resumer's resource
    and every lifetime its index reads; `freshI`, `FreshFrameI`: [TR] 6.112 at a block.
  - The equivariance the thaw needs: `TyEqInst`, `CohEInst`, `MutPayloadInst`, `InstEquivLeaf`
    (at types Core reads without a thunk, `CoreStable`), `ViewSlotInst`; why the leaf must tie the
    type, `ViewTypeCoincidence`; what `CoreStable` leaves out, `InstEquivLeafAll`,
    `MutPayloadInstAll`.
* **The known risk.** `Targets.NotVDenNaturalArises` (the `TW` history), `InternalPayloadArises`
  (the witness's shape with both lends on W's stack), `MutWitnessThaws` (the instantiation at
  it), and, beside them, `NotVCNaturalCore` (transport, as `FreezeBinderLife` states it, fails at
  a `coreW` world).
* **The `U` introductions retried.** The target is statement 0's four rows at the revised W
  (`Statement0UFull`). `Statement0UThawFree` is the partial form at the contexts `CtxThawFree`
  admits, and `ThawFreeScope` shows that typing reaches a context it excludes.

Definitions and `def … : Prop` statements only; no proofs. The statements over `vRL`, `gRL`,
`SemS`, `OwnOK`, `FutOK`, `LendMut` and `LendImm` are read at W as `BINDER.md` §5 revises them.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)

/-- `n` as a lifetime. -/
abbrev lifeN (n : ℕ) : Life := OrderDual.toDual n

/-! ### Bound places -/

/-- The innermost entry lending the place `l`, with its current lifetime. -/
def innerAt (σ : LStack) (αs : List Life) (l : BoCa.Loc) : Option (LEnt × Life) :=
  (σ.zip αs).find? fun p => decide (p.1.l = l)

/-- **A cell of `ρ` at `l`, at any depth**: at the top, or nested in the witness of one of its
cells. -/
inductive DeepAt : WRes → BoCa.Loc → CellU BoCa.Loc Val → Prop
  | top {ρ : WRes} {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} : ρ.get l = some ψ → DeepAt ρ l ψ
  | wit {ρ : WRes} {m l : BoCa.Loc} {φ ψ : CellU BoCa.Loc Val} :
      ρ.get m = some φ → DeepAt φ.wit l ψ → DeepAt ρ l ψ

/-- **A cell of `ρ` at `l` under no `imm` ancestor**: at the top, or nested only in the witnesses of
`mut` cells. These are the cells [TR] p. 5's exclusive walk `ex(ρ)` reaches, and a run's `↭` can
bring them to the top. -/
inductive ExAt : WRes → BoCa.Loc → CellU BoCa.Loc Val → Prop
  | top {ρ : WRes} {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} : ρ.get l = some ψ → ExAt ρ l ψ
  | wit {ρ : WRes} {m l : BoCa.Loc} {φ ψ : CellU BoCa.Loc Val} :
      ρ.get m = some φ → φ.kind = Kind.mut → ExAt φ.wit l ψ → ExAt ρ l ψ

/-- **PlaceViews at a configuration**, a shape read off the world's flattening. At a place whose
innermost lending entry is a 6.65 entry, the world's `mut` cell there is at the entry's current
lifetime and stores `𝒱⟦T⟧` of the entry's payload type, at some reading and list. At a 6.64
entry's place, the world's `imm` cell there is at the entry's current lifetime and holds the
entry's value. Its preservation along `Arises` is the arising check of `k` (`PVArises`). -/
def PlaceViewsW (σ : LStack) (αs : List Life) (fρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (e : LEnt) (α : Life), innerAt σ αs l = some (e, α) →
    ∀ ψ : CellU BoCa.Loc Val, fρ.FlatAt l ψ →
      (e.k = .mut → ψ.kind = Kind.mut → ψ.at = α ∧
        ∃ (δ' : LSub) (ls₀ : List SRec), mutPred ψ = fun v => vC true e.T ls₀ δ' v) ∧
      (∀ u, e.k = .imm u → ψ.kind = Kind.imm → ψ.at = α ∧ ψ.erase = u)

/-- **A cell exactly at `α`**: a `mut` cell's lifetime, and every lifetime of an `imm` cell's set,
is `α`. -/
def AtExactly (α : Life) (ψ : CellU BoCa.Loc Val) : Prop :=
  ψ.at = α ∧ ∀ t, ψ.lsOf = some t → ∀ y, t.mem y → y = α

/-- **W's view of one entry**: GhostEnd's view read at the reading `s` (the stack's), its cell
exactly at the entry's lifetime `α`. -/
def vwEW (s : LSub) (e : LEnt) (d : Bool) (α : Life) (ls : List SRec) : WProp := fun ρ =>
  vwE s e d α ls ρ ∧ ∀ ψ, ρ.get e.l = some ψ → AtExactly α ψ

/-- **W's views of a stack**, an entry whose place an inner entry lends again shadowed, as `vwS`. -/
def vwSW (s : LSub) : List BoCa.Loc → LStack → List Bool → List Life → List SRec → WProp
  | _, [], [], [], _ => emp
  | seen, e :: σ, d :: ds, α :: αs, ls =>
      vwEW s e (vis seen e d) α ls ⋆ vwSW s (e.l :: seen) σ ds αs ls
  | _, _, _, _, _ => fun _ => False

/-- **The top-level part of the guard**: every top-level borrow cell of `ρ` at a place the stack
lends is the innermost lending entry's view at the reading `s`, at the entry's exact lifetime. It
is what the thaw reads. -/
def PlaceViewsAt (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (ρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val), ρ.get l = some ψ → ψ.kind ≠ Kind.own →
    ∀ (e : LEnt) (α : Life), innerAt σ αs l = some (e, α) → vwEW s e true α ls (ResU.single l ψ)

/-- **W's guard conjunct**: every borrow cell of `ρ` under no `imm` ancestor (`ExAt`) at a place the
stack lends is the innermost lending entry's view, and every borrow cell at any depth (`DeepAt`) at
such a place is the view of an entry lending it; each at the reading `s`, at that entry's exact
lifetime. A run can bring a cell nested in a `mut` witness to the top, so the top-level part
(`PlaceViewsAt`) alone is not what the transitions keep. A cell frozen under an `imm` ancestor
can be an outer entry's view while an inner entry lends the place again. -/
def PlaceViewsL (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (ρ : WRes) : Prop :=
  (∀ (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val), ExAt ρ l ψ → ψ.kind ≠ Kind.own →
    ∀ (e : LEnt) (α : Life), innerAt σ αs l = some (e, α) →
      vwEW s e true α ls (ResU.single l ψ)) ∧
  ∀ (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val), DeepAt ρ l ψ → ψ.kind ≠ Kind.own →
    l ∈ σ.map LEnt.l → ∃ (e : LEnt) (α : Life), (e, α) ∈ σ.zip αs ∧ e.l = l ∧
      vwEW s e true α ls (ResU.single l ψ)

/-- **The guard's views give the top-level part**: `ExAt.top`. -/
def PVLTop : Prop :=
  ∀ (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (ρ : WRes),
    PlaceViewsL s σ αs ls ρ → PlaceViewsAt s σ αs ls ρ

/-- **W's views of a stack, at every depth**: the views, their nested cells at the stack's places
views as well. What the `U` clause drops and is handed back. -/
def vwSL (s : LSub) (σ : LStack) (ds : List Bool) (αs : List Life) (ls : List SRec) : WProp :=
  fun ρ => vwSW s [] σ ds αs ls ρ ∧ PlaceViewsL s σ αs ls ρ

/-- **W's guard, revised**: the stack's table and its views. It replaces `guardW` (`BINDER.md`
§5.1). -/
def guardPV (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (P : WProp) : WProp :=
  fun ρ => TabAtS σ αs ρ → PlaceViewsL s σ αs ls ρ → P ρ

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

/-- A callback's view type at its binder `x`, against the entry the own lend pushes (the revised
`OwnPush`'s last conjunct, `BINDER.md` §2.1). -/
def ViewAt (x : LifeVar) (e : LEnt) : VTy → Prop
  | .mut (.var y) T => y = x ∧ (match e.k with | .mut => True | .imm _ => False) ∧ e.T = T
  | .imm (.var y) T => y = x ∧ (match e.k with | .mut => False | .imm _ => True) ∧ e.T = T
  | _ => True

/-! ### The cut, internal lifetimes, and the records -/

/-- **The cut of a stack**: the lifetime just above its outermost lend (the outermost lend itself
when that is `⊤`). The empty stack has none. -/
def cutOf (αs : List Life) : Option Life :=
  αs.getLast?.map fun o => OrderDual.toDual (OrderDual.ofDual o - 1)

/-- **An internal lifetime** of a stack: strictly below its cut, so moved by an instantiation at
the cut and fixed by none other. Below `⊤` it is a lifetime at or below the outermost lend. -/
def Internal (αs : List Life) (a : Life) : Prop := ∃ c ∈ cutOf αs, a < c

/-- **An internal variable** of an index: one the stack's reading sends to an internal lifetime. An
instantiation at the stack's cut may move the values of these and fixes every other. -/
def InternalVar (δ : LSub) (σ : LStack) (αs : List Life) (y : LifeVar) : Prop :=
  ∃ m, (extS δ σ αs).find? y = some m ∧ Internal αs (OrderDual.toDual m)

/-- The outermost lend is below `⊤`, so it is internal. `OwnPush`'s bound puts every own lend
there (`OwnPushBelowTop`). -/
def OuterBelowTop (αs : List Life) : Prop := ∀ o ∈ αs.getLast?, o < ⊤

/-- **A record reads only lifetimes outliving the lends it outlives**: for each of the stack's
lends, every record strictly longer-lived than it reads, everywhere in its substitution, only
lifetimes strictly longer-lived than it. A lend fresh below every lifetime the records read
(`LendFresh`) opens with it, and a record made inside a lend is shorter-lived than that lend. So an
instantiation at the stack's cut, or at the cut of an inner part of the stack, leaves unchanged
every record outliving the lends it moves. -/
def RecsOutside (αs : List Life) (ls : List SRec) : Prop :=
  ∀ a ∈ αs, ∀ x ∈ ls, a < x.2 → ∀ p ∈ x.1.δ.entries, a < OrderDual.toDual p.2

/-- **Every record at or below the outermost lend is the stack's own**: it is in the lineage of the
record of one of the stack's 6.64 entries. A resume's re-lend rebuilds exactly these at the
instantiated reading and lifetimes. -/
def RecsInsideOwn (σ : LStack) (αs : List Life) (ls : List SRec) : Prop :=
  ∀ x ∈ ls, (∃ o ∈ αs.getLast?, x.2 ≤ o) →
    ∃ e ∈ σ, ∃ u, e.k = .imm u ∧ ∃ r ∈ rsOf ls, r.le = e.l ∧ DescR r x.1

/-- **A lend fresh below every lifetime the records read** ([TR] 6.112's `И`, taken below the
finite set of the records' frame lifetimes and readings). `LendMut` and `LendImm` carry it in the
revision (`BINDER.md` §5.1). -/
def LendFresh (ls : List SRec) (α : Life) : Prop :=
  ∀ x ∈ ls, α < x.2 ∧ ∀ p ∈ x.1.δ.entries, α < OrderDual.toDual p.2

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

/-- On the record list: a record whose frame lifetime is below the cut has its substitution and
frame lifetime moved; every other record is left as it is. A record's witness is kept, since no
resource is transported. -/
def recs : Inst → List SRec → List SRec
  | none, ls => ls
  | some ⟨c, θ⟩, ls => ls.map fun x =>
      if x.2 < c then (⟨x.1.le, x.1.v, x.1.R, x.1.T, Restrat.LSub.mapN θ.toNat x.1.δ⟩, θ x.2)
      else x

/-- The instantiation a re-stratification gives. -/
def ofEmb {c : Life} (θ : Restrat.Emb c) : Inst := some ⟨c, θ⟩

end Inst

/-- **The stack's instantiations**: the identity, or a re-stratification at the stack's cut. -/
def InstAt (αs : List Life) (ι : Inst) : Prop :=
  ∀ (c : Life) (θ : Restrat.Emb c), ι = some ⟨c, θ⟩ → cutOf αs = some c

/-- **W's `U` clause over instantiations, at the stack itself** (`binder0`). The resource splits into
the views it holds and a part strictly above the outermost lend. At every instantiation of the
stack's internal lifetimes, and every extension of the instantiated list that keeps
`RecsOutside`, that part, handed the views at the instantiated stack, is in `P` at the
instantiated reading. -/
def RelendI (δ : LSub) (σ : LStack) (P : LSub → List Life → List SRec → WProp)
    (αs : List Life) (ls : List SRec) : WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwSL (extS δ σ αs) σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ ι, InstAt αs ι → ∀ ls', Ext (ι.recs ls) ls' ρz → RecsOutside (ι.life αs) ls' →
      (vwSL (extS (ι.sub δ) σ (ι.life αs)) σ ds (ι.life αs) ls' ─⋆
        P (ι.sub δ) (ι.life αs) ls') ρz

/-- **W's `U` clause over instantiations and futures** (`cbpv`, `binder`): `RelendU` with the
re-lend replaced by an instantiation. -/
def RelendUI (fut own : Bool) (δ : LSub) (σ : LStack) (C : CTy)
    (P : LStack → LSub → List Life → List SRec → WProp) (αs : List Life) (ls : List SRec) :
    WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwSL (extS δ σ αs) σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ ι, InstAt αs ι → ∀ ls', Ext (ι.recs ls) ls' ρz → RecsOutside (ι.life αs) ls' →
      ∀ σ' αs'', FutQ fut (ι.sub δ) ρz (σ, ι.life αs) (σ', αs'') → FutAvoids C σ σ' →
        (vwSL (extS (ι.sub δ) σ (ι.life αs)) σ ds (ι.life αs) ls' ─⋆
          P σ' (ι.sub δ) αs'' ls') ρz ∧
        (own = true → ∀ (e : LEnt) (a : Life), OwnPush (ι.sub δ) C ρz (σ', αs'') e a →
          (vwSL (extS (ι.sub δ) σ (ι.life αs)) σ ds (ι.life αs) ls' ─⋆
            P (e :: σ') (ι.sub δ) (a :: αs'') ls') ρz)

/-! ### Internal variables -/

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

/-- **The syntactic description is inside the semantic one**: at an index that models `Δ`, at a
stack whose outermost lend is below `⊤`, a variable whose bound reaches below the stack is
internal. The converse does not hold, and the instantiation moves the other internal variables
too, which keeps `Δ`'s models (`InstModels`). -/
def InternalOfBound : Prop :=
  ∀ (Δ : LifeCtx) (δ : LSub) (σ : LStack) (αs : List Life) (y : LifeVar),
    StackOK σ αs → OuterBelowTop αs → Δ.Models (extS δ σ αs) → BoundBelowV Δ σ y →
    InternalVar δ σ αs y

/-- **An own lend is below `⊤`**: `OwnPush` reads the bound's `LtLife`, `a ⊏ @c ⊑ ⊤`. -/
def OwnPushBelowTop : Prop :=
  ∀ (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (e : LEnt) (a : Life), OwnPush δ C ρ s e a → a < ⊤

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

/-- **A lifetime an index reads**: a lend lifetime, a value of the reading substitution, or a
record's frame lifetime or a value of its substitution. A finite set. -/
def IdxReads (δ : LSub) (αs : List Life) (ls : List SRec) (a : Life) : Prop :=
  a ∈ αs ∨ (∃ p ∈ δ.entries, a = OrderDual.toDual p.2) ∨
    ∃ x ∈ ls, a = x.2 ∨ ∃ p ∈ x.1.δ.entries, a = OrderDual.toDual p.2

/-- **A fresh instantiation**: every lifetime it moves lands strictly below every cell of the
resumer's resource `R` and every lifetime the resumer's index `(δ, αs, ls)` reads. -/
def InstFresh (R : WRes) (δ : LSub) (αs : List Life) (ls : List SRec) : Inst → Prop
  | none => True
  | some ⟨c, θ⟩ => ∀ a, a < c → R.InStratum (θ a) ∧ ∀ b, IdxReads δ αs ls b → θ a < b

/-- **Fresh instantiations exist** at every stack with a cut, below every resumer's resource and
index. The proof is arithmetic: `Restrat.Emb.shift c k` past the finite set's largest value
(`Restrat.Emb.shift_fresh`). -/
def InstFreshExists : Prop :=
  ∀ (αs : List Life) (R : WRes) (δ : LSub) (αsR : List Life) (lsR : List SRec) (c : Life),
    cutOf αs = some c → ∃ θ : Restrat.Emb c, InstFresh R δ αsR lsR (Inst.ofEmb θ)

/-- **`И` at a block of lifetimes** (ours): a bound such that every instantiation at the cut `c`
whose moved lifetimes lie below it has `Q`, the resource lying above the moved lifetimes. [TR] p. 6's
`И P̂ ≜ ∃β. ∀α ⊏ β. [α] P̂(α)`, at a block. -/
def freshI (c : Life) (Q : Restrat.Emb c → WProp) : WProp := fun ρ =>
  ∃ β : Life, ∀ θ : Restrat.Emb c, (∀ a, a < c → θ a < β) →
    Q θ ρ ∧ ∀ a, a < c → ρ.InStratum (θ a)

/-- **[TR] 6.112 at a block**: `P ⋆ Иθ. Q(θ) ⊨ Иθ. ([θ] P ⋆ Q(θ))`, the form the share reaches for
at a resume. Its proof is `fresh_frame`'s at a block: the bound `@ρ_P ⊓ β_Q`, by the chain 6.101,
6.99, 6.100, 6.111. -/
def FreshFrameI : Prop :=
  ∀ (c : Life) (P : WProp) (Q : Restrat.Emb c → WProp) (ρ : WRes),
    (P ⋆ freshI c Q) ρ →
      freshI c (fun θ => (fun ρ₁ => P ρ₁ ∧ ∀ a, a < c → ρ₁.InStratum (θ a)) ⋆ Q θ) ρ

/-! ### Bookkeeping the rows read at an instantiation -/

/-- **An instantiation of a stack in shape is a re-lend of it** (`ReLend`): it lowers each lend
lifetime and keeps their nesting order. -/
def InstReLend : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ι : Inst), StackOK σ αs → InstAt αs ι → ReLend (ι.life αs) αs

/-- **The stack's reading commutes with an instantiation.** -/
def ExtSInst : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ι : Inst), αs.length = σ.length →
    extS (ι.sub δ) σ (ι.life αs) = ι.sub (extS δ σ αs)

/-- **A re-stratification at a lower cut is one at a higher cut**: it fixes every lifetime at or
above the higher cut. -/
def EmbLift : Prop :=
  ∀ (c c' : Life) (θ : Restrat.Emb c'), c' ≤ c → ∃ θ' : Restrat.Emb c, ∀ x, θ' x = θ x

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

/-- **An instantiation keeps `RecsOutside`**: the moved records and the moved lends move together,
and a record left alone outlives every moved lend. -/
def RecsOutsideInst : Prop :=
  ∀ (αs : List Life) (ls : List SRec) (ι : Inst), InstAt αs ι → RecsOutside αs ls →
    RecsOutside (ι.life αs) (ι.recs ls)

/-- **The stack's entries in a judgement are entries of it at an instantiation**: the own lend's
bound is read at the instantiated reading (`Restrat.Emb.ltLife_mapN_iff`). -/
def StackJInst : Prop :=
  ∀ (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (ι : Inst),
    αs.length = σ.length → StackJ σ αs δ Δ Γ C → StackJ σ (ι.life αs) (ι.sub δ) Δ Γ C

/-- **The narrowing's cost, met at the share**: the share re-lends the ghost-ended inner entries
`αi` at an instantiation `θ` of their cut, which the resume chooses (`InstFreshExists`). As an
instantiation of the continuation's whole stack `αi ++ αo` it moves the ended lifetimes, fixes the
kept ones, reads the same substitution, and, under `RecsOutside`, moves the same records. So every
re-lend at which the share hands a captured `U` value its views is one `RelendI` covers. -/
def ShareReLendInst : Prop :=
  ∀ (αi αo : List Life) (ls : List SRec) (ci : Life) (θ : Restrat.Emb ci), cutOf αi = some ci →
    List.IsChain (· < ·) (αi ++ αo) → RecsOutside (αi ++ αo) ls →
    ∃ ι : Inst, InstAt (αi ++ αo) ι ∧ ι.life (αi ++ αo) = (Inst.ofEmb θ).life αi ++ αo ∧
      (∀ δ, ι.sub δ = (Inst.ofEmb θ).sub δ) ∧ ι.recs ls = (Inst.ofEmb θ).recs ls

/-- **A configuration that arises carries its frame, its local part and a valid world.** -/
def ArisesInv : Prop :=
  ∀ c : Cfg, Arises (ℍ := ℍ) c →
    ResU.Hash c.ρf c.ρ ∧ ResU.CompS c.ρf c.ρ c.fρ ∧ ResU.Valid c.fρ

/-- **The records' invariants arise**, at the revised `Arises` whose lends carry `LendFresh`. -/
def RecsOutsideArises : Prop := ∀ c : Cfg, Arises (ℍ := ℍ) c → RecsOutside c.αs c.ls

def RecsInsideOwnArises : Prop := ∀ c : Cfg, Arises (ℍ := ℍ) c → RecsInsideOwn c.σ c.αs c.ls

/-! ### The guard's run invariant: the local bundle -/

/-- At the empty stack no place is bound. -/
def PVLNil : Prop := ∀ (s : LSub) (ls : List SRec) (ρ : WRes), PlaceViewsL s [] [] ls ρ

/-- **Parts and whole.** -/
def PVLParts : Prop :=
  ∀ (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (ρ₁ ρ₂ ρ : WRes),
    ResU.CompS ρ₁ ρ₂ ρ →
      (PlaceViewsL s σ αs ls ρ ↔ PlaceViewsL s σ αs ls ρ₁ ∧ PlaceViewsL s σ αs ls ρ₂)

/-- **`↭` keeps the guard's views.** [TR] 6.48's case analysis at the local part: a cell outside
every `imm` ancestor by `↭`'s `mut` clause at the flattening, a cell under an `imm` ancestor
through that ancestor, which `↭`'s `imm` clause keeps whole, and `○` idempotent at one stored
invariant. -/
def PVLUpd : Prop :=
  ∀ (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (ρ π : WRes), StackOK σ αs →
    PlaceViewsL s σ αs ls ρ → ResU.UpdV ρ π → PlaceViewsL s σ αs ls π

/-- **Every run keeps the guard's views**: `PVLUpd` read through `wpG`'s run-end conjunct, with
`PVLParts` at the run's local part; the list's members are kept, and the views read only them. -/
def PVLRuns : Prop :=
  ∀ (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (e : Expr)
    (Q : List SRec → Expr → WProp) (ρ : WRes), StackOK σ αs → PlaceViewsL s σ αs ls ρ →
    wpG (ℍ := ℍ) ls e Q ρ →
      wpG (ℍ := ℍ) ls e (fun ls' t ρ' => PlaceViewsL s σ αs ls' ρ' ∧ Q ls' t ρ') ρ

/-- **The start of a lend**: the callback's resource, holding no cell at the lent place at any
depth, joined to the lend's view, whose nested cells at the stack's places are views as well, has
the guard's views at the pushed stack, read at the pushed reading. The pushed reading agrees with
the old one at the old entries' payload types. The lend row supplies the view: 6.65's cell at
exactly `α` storing `𝒱⟦T⟧`, or 6.64's `imm({α}, v, R)` with `R ∈ 𝒱⟦T⟧(v)` from its lender's
owner. -/
def PVLStart : Prop :=
  ∀ (s s' : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (e : LEnt) (α : Life)
    (ρ a R : WRes), StackOK σ αs → List.IsChain (· < ·) (α :: αs) → e.l ∉ σ.map LEnt.l →
    (∀ e' ∈ σ, ∀ y, VFree y e'.T → s'.find? y = s.find? y) →
    PlaceViewsL s σ αs ls ρ → (∀ ψ, ¬ DeepAt ρ e.l ψ) →
    vwEW s' e true α ls a → PlaceViewsL s' (e :: σ) (α :: αs) ls a →
    ResU.CompS ρ a R → PlaceViewsL s' (e :: σ) (α :: αs) ls R

/-- **A handler keeps the guard's views**: they read no entry's row. -/
def PVLHide : Prop :=
  ∀ (N : UInt32 → Bool) (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (ρ : WRes),
    PlaceViewsL s σ αs ls ρ → PlaceViewsL s (hideS N σ) αs ls ρ

/-- **A future keeps the guard's views**: the inserted entries' places are new and hold no cell of
the resource (the revised `FutOK.placesFree`), the old entries' payload types read the same, and
the list's records above the resource's cells are kept. -/
def PVLFut : Prop :=
  ∀ (δ : LSub) (σ σ' : LStack) (αs αs' : List Life) (ls ls' : List SRec) (ρ : WRes),
    StackOK σ αs → Fut δ ρ (σ, αs) (σ', αs') → Ext ls ls' ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → PlaceViewsL (extS δ σ' αs') σ' αs' ls' ρ

/-- **The table and the guard's views at an instantiation**: a part above the outermost lend, handed
W's views at the instantiated stack, has the table and the guard's views there. -/
def GuardInst : Prop :=
  ∀ (δ : LSub) (σ : LStack) (ds : List Bool) (αs : List Life) (ls ls' : List SRec)
    (ρz ρn ρ ρv R : WRes) (ι : Inst),
    StackOK σ αs → InstAt αs ι → stratS αs ρz → vwSL (extS δ σ αs) σ ds αs ls ρn →
    ResU.CompS ρz ρn ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vwSL (extS (ι.sub δ) σ (ι.life αs)) σ ds (ι.life αs) ls' ρv → ResU.CompS ρz ρv R →
    TabAtS σ (ι.life αs) R ∧ PlaceViewsL (extS (ι.sub δ) σ (ι.life αs)) σ (ι.life αs) ls' R

/-- **The resume composite keeps the guard's views**: the continuation's share, above the outermost
lend of its stack `σi ++ σo`, handed the views of the re-lent inner entries `σi`, joined to the
handler's answer resource, which has the guard's views at the kept part `σo` and no cell at the
inner entries' places. -/
def PVLResume : Prop :=
  ∀ (s : LSub) (σi σo : LStack) (ds : List Bool) (αi αo : List Life) (ls : List SRec)
    (ρz ρv ρa R R' : WRes),
    StackOK (σi ++ σo) (αi ++ αo) → stratS (αi ++ αo) ρz →
    PlaceViewsL s (σi ++ σo) (αi ++ αo) ls ρz → vwSW s [] σi ds αi ls ρv →
    PlaceViewsL s (σi ++ σo) (αi ++ αo) ls ρv → PlaceViewsL s σo αo ls ρa →
    (∀ e ∈ σi, ∀ ψ, ¬ DeepAt ρa e.l ψ) → ResU.CompS ρz ρv R → ResU.CompS R ρa R' →
    PlaceViewsL s (σi ++ σo) (αi ++ αo) ls R'

/-- **The guard's views are the stack's run invariant**: one fact per transition of W's semantics
(the nil index, a part, a run, a lend's start, a handler) and per configuration the relation
quantifies over (an instantiation, a future, the resume composite). -/
def PVLBundle : Prop :=
  PVLNil ∧ PVLParts ∧ PVLUpd ∧ PVLRuns (ℍ := ℍ) ∧ PVLStart ∧ PVLHide ∧ GuardInst ∧ PVLFut ∧
    PVLResume

/-! ### The equivariance the thaw needs -/

/-- **`TyEq` is kept by an instantiation of both readings.** -/
def TyEqInst : Prop :=
  ∀ (A B : VTy) (s s' : LSub) (ι : Inst), TyEq A s B s' → TyEq A (ι.sub s) B (ι.sub s')

/-- **Coherence survives an instantiation**: `CohE` against a moved record by `TyEqInst`, against
a record left alone because it reads only lifetimes the instantiation fixes (`RecsOutside`). -/
def CohEInst : Prop :=
  ∀ (αs : List Life) (ls : List SRec) (m : BoCa.Loc) (A : VTy) (s : LSub) (c : Life)
    (θ : Restrat.Emb c), cutOf αs = some c → RecsOutside αs ls → CohE (rsOf ls) m A s →
    CohE (rsOf ((Inst.ofEmb θ).recs ls)) m A ((Inst.ofEmb θ).sub s)

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

/-- **A slot type the thaw handles at the partial result**: W's own formers down to `U`, which W
instantiates by construction, and leaves whose payloads Core reads without a thunk. `μ` and `fam`
are handed to Core's relation whole, and its `U` clause is not instantiated. -/
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

/-- A context the partial result handles: every live slot's type is `ThawFree`. A guarantee gap:
FL at W proved only under it says nothing of a thunk over a `μ` or `fam` slot inside a lend. -/
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

/-- **A record the instantiation at `c` leaves alone, reading only lifetimes it fixes.** -/
def RecFixed (c : Life) (x : SRec) : Prop :=
  c ≤ x.2 ∧ ∀ p ∈ x.1.δ.entries, c ≤ OrderDual.toDual p.2

/-- **A supported `Mut` payload is fixed by an instantiation whose cut is at or below its stratum.**
This is the case of `mut_not_natural`'s shape that the instantiation meets: the cell is not moved,
and its stored invariant is re-read at the instantiated reading. The records it reads are those
longer-lived than the cell, which the instantiation leaves alone. -/
def MutPayloadInst : Prop :=
  ∀ (T : VTy) (ls₀ : List SRec) (s : LSub) (b c : Life) (θ : Restrat.Emb c), CoreStable T →
    c ≤ b → (∀ x ∈ ls₀, RecFixed c x) → (∀ ls' u σ', vC true T ls' s u σ' → σ'.InStratum b) →
    ∀ u σ', vC true T (Inst.recs (Inst.ofEmb θ) ls₀) (Inst.sub (Inst.ofEmb θ) s) u σ' ↔
      vC true T ls₀ s u σ'

/-- **`MutPayloadInst` at every payload type**: the excluded case of the partial result. At
`T = U C` it is the `Mut (U C)` leaf at an instantiation, where Core's `U` clause reads its
argument contravariantly (`Restrat.Open.WpNatural`'s question). Stated, not derived. -/
def MutPayloadInstAll : Prop :=
  ∀ (T : VTy) (ls₀ : List SRec) (s : LSub) (b c : Life) (θ : Restrat.Emb c),
    c ≤ b → (∀ x ∈ ls₀, RecFixed c x) → (∀ ls' u σ', vC true T ls' s u σ' → σ'.InStratum b) →
    ∀ u σ', vC true T (Inst.recs (Inst.ofEmb θ) ls₀) (Inst.sub (Inst.ofEmb θ) s) u σ' ↔
      vC true T ls₀ s u σ'

/-- **Core's relation is kept by an instantiation at a resource it fixes**: at a type read without a
thunk, at a resource all of whose cells are at or above the cut, it holds at the instantiated
reading and list. W's leaves off the stack's places, at the part a `U` value retains, are its
instances. -/
def InstEquivLeaf : Prop :=
  ∀ (A : VTy) (b : Bool) (αs : List Life) (ls : List SRec) (s : LSub) (v : Val) (ρ : WRes)
    (c : Life) (θ : Restrat.Emb c), cutOf αs = some c → RecsOutside αs ls → CoreStable A →
    StratumLe ρ c → vCE none b A ls s v ρ →
    vCE none b A (Inst.recs (Inst.ofEmb θ) ls) (Inst.sub (Inst.ofEmb θ) s) v ρ

/-- **`InstEquivLeaf` at every type**: the excluded case of the partial result (`μ`, `fam`, a thunk
inside a `Mut` or `Imm` payload). Stated, not derived. -/
def InstEquivLeafAll : Prop :=
  ∀ (A : VTy) (b : Bool) (αs : List Life) (ls : List SRec) (s : LSub) (v : Val) (ρ : WRes)
    (c : Life) (θ : Restrat.Emb c), cutOf αs = some c → RecsOutside αs ls →
    StratumLe ρ c → vCE none b A ls s v ρ →
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

/-! ### The arising check of `k`: PlaceViews at the world -/

/-- At the empty stack there is no bound place. -/
def PVWNil : Prop := ∀ W : WRes, PlaceViewsW [] [] W

/-- **`↭` keeps PlaceViews at the world**: its `mut` clause keeps a `mut` cell's lifetime and
invariant at the flattening, its `imm` clause keeps an `imm` cell. -/
def PVWUpd : Prop :=
  ∀ (σ : LStack) (αs : List Life) (W W' : WRes), PlaceViewsW σ αs W → ResU.UpdV W W' →
    PlaceViewsW σ αs W'

/-- **A run keeps PlaceViews at the world**: [TR] 6.48 carries the run's `↭` on the local part to
the world (the frame `ρ_f`, the garbage joining it), and `PVWUpd` applies there. -/
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

/-- **A handler keeps PlaceViews at the world**: it reads no entry's row. -/
def PVWHide : Prop :=
  ∀ (N : UInt32 → Bool) (σ : LStack) (αs : List Life) (W : WRes), PlaceViewsW σ αs W →
    PlaceViewsW (hideS N σ) αs W

/-- **PlaceViews holds at the world of every configuration that arises.** It is used only to
exclude `k`. -/
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

/-- **`k`'s slot fails W's `Mut` leaf**: its payload `1` is not the entry's `Unk` up to the reading
(`CohS`). With `KNotViewAt`, `k_reached`'s third conjunct is false at W. -/
def KSlotNotW : Prop :=
  ∀ δ : LSub, ¬ CohS kσ [kα] (extS δ kσ [kα]) (.mut (.var 0) .unit) (.loc 0) kρ

/-- **`k`'s entry is not the own lend at `kC`** under the revised `OwnPush`: its payload `Unk` is not
the callback's view payload `1`. -/
def KNotViewAt : Prop := ¬ ViewAt 0 kEnt (.mut (.var 0) .unit)

/-! ### The known risk: `mut_not_natural` -/

/-- **The shape of `mut_not_natural`'s witness arises at W**: a 6.65 entry `x` at `2` whose payload
type is `Imm 'b 1`, `'b` the variable of a 6.64 entry `b` at `1` outside it, both on the stack. The
cell at `x`'s place is `x`'s view at the stack's reading, its witness holds `b`'s `imm` cell at
`1`, and the place is a value that arises at `x`'s view type. Evidence that the shape is reachable,
not a refutation. -/
def InternalPayloadArises : Prop :=
  ∃ (c : Cfg) (x b : LEnt) (u : Val) (δ : LSub) (ψ ψb : CellU BoCa.Loc Val) (ρf' : WRes),
    Arises (ℍ := ℍ) c ∧ c.σ = [x, b] ∧ c.αs = [lifeN 2, lifeN 1] ∧ x.k = .mut ∧ b.k = .imm u ∧
    x.T = .imm (.var b.x) .unit ∧ c.ρ.get x.l = some ψ ∧
    vwEW (extS δ c.σ c.αs) x true (lifeN 2) c.ls (ResU.single x.l ψ) ∧
    ψ.wit.get b.l = some ψb ∧ ψb.kind = Kind.imm ∧ ψb.at = lifeN 1 ∧
    ArisesV (ℍ := ℍ) (c.at ρf' (ResU.single x.l ψ)) (.loc x.l) (viewTy x)

/-- `InternalPayloadArises`'s entries, at concrete places and variables: `x` lends the place `0` at
`'0`, payload `Imm '1 1`; `b` lends the place `1` at `'1`, payload `1`, kind `imm ()`. -/
abbrev mwX : LEnt := ⟨0, 0, .imm (.var 1) .unit, .mut, fun _ => true⟩

abbrev mwB : LEnt := ⟨1, 1, .unit, .imm .unit, fun _ => true⟩

abbrev mwσ : LStack := [mwX, mwB]

abbrev mwαs : List Life := [lifeN 2, lifeN 1]

/-- The slot's type, `Mut '0 (Imm '1 1)`: `mut_not_natural`'s `T`. -/
abbrev mwTy : VTy := .mut (.var 0) (.imm (.var 1) .unit)

/-- The witness's own map, `n ↦ n + 1` below `⊤`, as an instantiation of `mwσ`, whose cut is `⊤`. -/
abbrev mwι : Inst := Inst.ofEmb (Restrat.Emb.shift ⊤ 1)

/-- **`ViewSlotInst` at the witness**: at `mut_not_natural`'s own map, the slot holding `x`'s view
at `Mut '0 (Imm '1 1)` is re-established from the view handed at the instantiated reading. It is
meant at `InternalPayloadArises`'s configuration, the slot `m` holding `x`'s view. -/
def MutWitnessThaws : Prop :=
  InstAt mwαs mwι ∧
  ∀ (δ : LSub) (ls ls' : List SRec) (ρ ρv : WRes), mwι.recs ls ⊆ ls' →
    vC true mwTy ls (extS δ mwσ mwαs) (.loc mwX.l) ρ →
    CohS mwσ mwαs (extS δ mwσ mwαs) mwTy (.loc mwX.l) ρ →
    vwEW (mwι.sub (extS δ mwσ mwαs)) mwX true (mwι.life1 (lifeN 2)) ls' ρv →
    vC true mwTy ls' (mwι.sub (extS δ mwσ mwαs)) (.loc mwX.l) ρv ∧
      CohS mwσ (mwι.life mwαs) (mwι.sub (extS δ mwσ mwαs)) mwTy (.loc mwX.l) ρv

/-- **Beside: transport fails at a `coreW` world.** A resource that is part of a tagged `TW` world,
at which Core's relation holds, and at which it fails once the resource, the reading and the
records are moved along `shift ⊤ 1` (`Restrat.Emb.relRU`, `Targets.srecRestrat`), as
`Targets.FreezeBinderLife`'s `val` clause moves them. The world is required; the value is not
required to arise. -/
def NotVCNaturalCore : Prop :=
  ∃ (fρ ρf ρ : WRes) (ps : List FrameRec) (ls : List SRec) (T : VTy) (δ : LSub) (v : Val),
    (Targets.coreW (ℍ := ℍ)).Fam fρ ps (ls, ()) ∧ ResU.CompS ρf ρ fρ ∧ vC true T ls δ v ρ ∧
    ¬ vC true T (ls.map (Targets.srecRestrat (Restrat.Emb.shift ⊤ 1)))
      (Restrat.LSub.mapN (Restrat.Emb.shift ⊤ 1).toNat δ) v ((Restrat.Emb.shift ⊤ 1).relRU ρ)

/-- **It refutes `FreezeBinderLife` at `coreW` as Targets states it**, at every action on `coreW`'s
stacks: its `val` clause fails at that configuration. A fact about that statement. -/
def NotVCNaturalCoreRefutes : Prop :=
  NotVCNaturalCore (ℍ := ℍ) →
    ∀ a : Targets.StkAct (Targets.coreW (ℍ := ℍ)), ¬ Targets.FreezeBinderLife (Targets.coreW (ℍ := ℍ)) a

/-! ### The `U` introductions retried -/

/-- **The context's thaw over instantiations**, at one row's context: at every index `SemS` admits,
the guard's views and the records' invariant included, a context related at the stack is
re-lendable over instantiations. -/
def CtxRelendableAtI (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → SubDom δ Δ → Δ.Models (extS δ σ αs) → RecsOutside αs ls → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gRL p σ δ αs ls Γ γ ρ →
    RelendI δ σ (fun δ' αs' ls' => gRL p σ δ' αs' ls' Γ γ) αs ls ρ

/-- **The thaw at every context**: the target. -/
def CtxRelendsAll (p : Placement) : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), CtxRelendableAtI p Δ Γ

/-- **The thaw at the contexts the partial result handles.** -/
def CtxRelendsThawFree (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy), CtxThawFree Γ → CtxRelendableAtI p Δ Γ

/-- **A `U` value instantiated is a `U` value at the instantiation** (`ThawRelend` over
instantiations). -/
def ThawInst (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec) (f : Val) (ρ : WRes),
    StackOK σ αs → RecsOutside αs ls → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRL p σ δ (.thunk C) αs ls f ρ →
    RelendI δ σ (fun δ' αs' ls' => vRL p σ δ' (.thunk C) αs' ls' f) αs ls ρ

/-- **The `U` side of statement 0 at the revised W**: the target. The four rows are statement 0's
own (`ThunkFRow` …), read at the revised W, with the thaw at every context. -/
def Statement0UFull (p : Placement) : Prop :=
  ThawInst (ℍ := ℍ) p ∧ CtxRelendsAll (ℍ := ℍ) p ∧ ThunkFRow (ℍ := ℍ) p ∧
    ThunkVRow (ℍ := ℍ) p ∧ BangThunkFRow (ℍ := ℍ) p ∧ BangThunkVRow (ℍ := ℍ) p

/-- **`thunk M : U (F A)`** at a context the partial result handles. -/
def ThunkFRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxThawFree Γ →
    SemS p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemS p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))

/-- **`thunk V : U C`** at a context the partial result handles. -/
def ThunkVRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxThawFree Γ → C.isRet = false →
    OwnHyg Δ Γ C → SemS p Δ Γ (.val (.lam N)) (.comp C) →
    SemS p Δ Γ (.val (.lam N)) (.val (.thunk C))

/-- **`!thunk M : !U (F A)`** at a persistent context the partial result handles. -/
def BangThunkFRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxThawFree Γ → Persistent Γ →
    SemS p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemS p Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))

/-- **`!thunk V : !U C`** at a persistent context the partial result handles. -/
def BangThunkVRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxThawFree Γ → Persistent Γ →
    C.isRet = false → OwnHyg Δ Γ C → SemS p Δ Γ (.val (.lam N)) (.comp C) →
    SemS p Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

/-- **The `U` side of statement 0 at the contexts `CtxThawFree` admits**: the partial result,
guarantee gap R1 (`μ`, `fam`) open. -/
def Statement0UThawFree (p : Placement) : Prop :=
  ThawInst (ℍ := ℍ) p ∧ CtxRelendsThawFree (ℍ := ℍ) p ∧ ThunkFRowTF (ℍ := ℍ) p ∧
    ThunkVRowTF (ℍ := ℍ) p ∧ BangThunkFRowTF (ℍ := ℍ) p ∧ BangThunkVRowTF (ℍ := ℍ) p

/-- `μX. 1 ⊕ X`, a list of units: a slot type `CtxThawFree` excludes. -/
abbrev listTy : VTy := .mu (.sum .unit (.tvar 0))

/-- The type of `Λ'0. λm. λxs. thunk (return (m, xs))`:
`∀'0 ⊏ ⊤. Mut '0 1 ⊸ μX. 1 ⊕ X ⊸ F (U (F (Mut '0 1 ⊗ μX. 1 ⊕ X)))`. -/
abbrev scopeC : CTy :=
  .all 0 .top (.arr (.mut (.var 0) .unit)
    (.arr listTy (.ret (.thunk (.ret (.tensor (.mut (.var 0) .unit) listTy))))))

/-- The context at the thunk: `xs : μX. 1 ⊕ X`, `m : Mut '0 1`, the `∀`'s slot dead. -/
abbrev scopeΓ : Ctx VTy := [⟨listTy, true⟩, ⟨.mut (.var 0) .unit, true⟩, ⟨.unit, false⟩]

/-- **`CtxThawFree` excludes a context typing reaches inside a lend.** The closed term
`Λ'0. λm. λxs. thunk (return (m, xs))` is derived at `scopeC`. Read at `[]`, `binder0`'s `∀`
clause pushes the own lend of `'0` (`OwnPush`, payload `1`, `qEnt`), and at the pushed stack the
`U` introduction sits at `scopeΓ`, whose live slot `xs` is a `μ` and whose live slot `m` is the
lend's view. So the partial result says nothing of this thunk. -/
def ThawFreeScope : Prop :=
  CDerives LifeCtx.empty []
      (.val (.lam (.val (.lam (.val (.lam (.val (.lam (.pair (.var 2) (.var 1))))))))))
      (.comp scopeC) ∧
    CDerives kΔ scopeΓ (.val (.lam (.pair (.var 2) (.var 1))))
      (.val (.thunk (.ret (.tensor (.mut (.var 0) .unit) listTy)))) ∧
    OwnPush kδ scopeC PMap.empty ([], []) qEnt kα ∧ ¬ CtxThawFree scopeΓ

end ProbeD1

end
