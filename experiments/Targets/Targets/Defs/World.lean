import Core.Fundamental
import Targets.Defs.Effects

/-!
# Targets — the world W, abstractly (DESIGN §1.3–§1.4)

The signed-off structure says what W is: one Kripke world `W = (ρ, ls, σ)`, resource × record list
× lend stack.  Effects change three things in BoLo: the world, the wp's stop condition, and the
relation at effect rows.  `SemWorld` has exactly those as fields, and two more: `held`, what the
suspended computations at an index hold, and `payStk`, the lend stack a cell's stored payload is
read at (OQ-46).  Everything else is defined from them the way Core defines it, with
`TW … ∧ Tagged …` replaced by `M.Fam`, R-T1 by `M.Stop`, and a record list by an index.

`coreW` is Core's relation as a world whose lend stack has one point, and the transports
(`wpGW_core`, `ewpW_core`, `opTabW_core`, `cancelTabW_core`, `ptoMutSW_core`, `ptoImmSW_core`,
`gDenW_core`, `semW₀_core`) say that each derived definition at `coreW` is Core's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Indices, tables, the world -/

/-- The index of `W = (ρ, ls, σ)`: the record list and the lend stack.  The resource `ρ` is the
argument of every `WProp`. -/
abbrev Idx (Stk : Type) := List SRec × Stk

/-- Core's protocol tables (`Table`), at any index. -/
abbrev TableI (I : Type) := I → Expr → (I → Expr → WProp) → WProp

/-- A table is monotone in the continuations it owes. -/
def TableI.Mono {I : Type} (Tb : TableI I) : Prop :=
  ∀ i t (Φ Φ' : I → Expr → WProp) ρ, (∀ i e ρ, Φ i e ρ → Φ' i e ρ) → Tb i t Φ ρ → Tb i t Φ' ρ

/-- A table that owes no continuation. -/
def TableI.Abortive {I : Type} (Tb : TableI I) : Prop :=
  ∀ i t (Φ Φ' : I → Expr → WProp) ρ, Tb i t Φ ρ → Tb i t Φ' ρ

/-- An operation's entry (`OpEnt`), at any index. -/
structure OpEntI (I : Type) where
  q : Qual
  abort : Bool
  PA : I → Val → WProp
  PB : I → Val → WProp

/-- An operation table (`OpTab`), at any index. -/
abbrev OpTabI (I : Type) := UInt32 → UInt32 → Option (OpEntI I)

/-- **The planned world W, abstractly.**  `coreW` is the instance whose lend stack has one
point. -/
structure SemWorld where
  /-- σ.  What a lend stack holds is OQ-44's question; here it is a type. -/
  Stk   : Type
  nil   : Stk
  /-- What the suspended computations at an index hold: their open 6.64 frames and their tagged
  records.  Where they are kept is OQ-9's question; under its option (b) nothing is held. -/
  held  : Idx Stk → List FrameRec × List SRec
  /-- The configurations W reaches at an index: the full resource and the open 6.64 frames visible
  to the running computation. -/
  Fam   : WRes → List FrameRec → Idx Stk → Prop
  /-- The stop condition: entry frames/index, exit frames/index, final term.  Core's is R-T1. -/
  Stop  : List FrameRec × Idx Stk → List FrameRec × Idx Stk → Expr → Prop
  /-- The Kripke order on indices, relative to a resource (Core's `Ext`). -/
  Ext   : Idx Stk → Idx Stk → WRes → Prop
  /-- What a stop at a resuming operation owes its continuation (Core's `contShare`). -/
  share : OpTabI (Idx Stk) → OpEntI (Idx Stk) → UInt32 → Idx Stk → Kont →
            (Idx Stk → Expr → WProp) → WProp
  /-- The lend stack at which a cell at lifetime `b` reads its stored payload, given the stack of
  the index the cell is read at (OQ-46). -/
  payStk : Life → Stk → Stk
  /-- The relation, mode-indexed as `vCE` is. -/
  val   : Bool → VTy → Idx Stk → LSub → Val → WProp
  comp  : CTy → Idx Stk → LSub → Expr → WProp

/-! ### Derived definitions -/

/-- `ℓ ↦ M_α P` at W: `ptoMutS` with the stored predicate read at the index
`(ls₀, M.payStk b i.2)`, `ls₀` the records of `i.1` strictly longer-lived than the cell. -/
def ptoMutSW (M : SemWorld) (l : Loc) (α : Life) (i : Idx M.Stk) (P : Idx M.Stk → Val → WProp) :
    WProp := fun ρ =>
  ∃ (b : Life) (u : Val) (σ : WRes) (h : σ.InStratum b) (Q : Val → SPropS Loc Val b)
    (hw : Q u ⟨σ, h⟩) (ls₀ : List SRec),
    α ⊑ b ∧ ρ = ResU.single l (CellU.mutOf b u σ h Q hw) ∧ ofS Q = P (ls₀, M.payStk b i.2) ∧
    (∀ x, x ∈ ls₀ ↔ (x ∈ i.1 ∧ x.2 ⊐ b)) ∧ ∀ i' u' σ', P i' u' σ' → σ'.InStratum b

/-- `ℓ ↦ I_α P` at W: `ptoImmS` the same way, at the cell's `⊓β̄`. -/
def ptoImmSW (M : SemWorld) (l : Loc) (α : Life) (i : Idx M.Stk) (P : Idx M.Stk → Val → WProp) :
    WProp := fun ρ =>
  ∃ (s : LSet) (u : Val) (σ : WRes) (h : σ.InStratum s.join) (ls₀ : List SRec),
    ρ = ResU.single l (CellU.immOf s u σ h) ∧ P (ls₀, M.payStk s.meet i.2) u σ ∧ α ⊑ s.meet ∧
    ∀ x, x ∈ ls₀ ↔ (x ∈ i.1 ∧ x.2 ⊐ s.meet)

/-- W's one-run wp: `wpG` over `M.Fam`, ending under `M.Stop`. -/
def wpGW (M : SemWorld) (i : Idx M.Stk) (e : Expr) (Q : Idx M.Stk → Expr → WProp) : WProp :=
  fun ρ => ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    M.Fam fρ ps i → ∀ (A : Alloc) (k : Nat),
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (t : Expr) (μ μ' : Heap) (ps' : List FrameRec)
      (i' : Idx M.Stk),
      ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧ ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧ (∃ k', ARun (ℍ := ℍ) A k μ e k' μ' t) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧ NoOwn ρp ∧
      M.Fam fρ'p ps' i' ∧ M.Stop (ps, i) (ps', i') t ∧ Q i' t ρ'

/-- The postcondition over terms that admits only values. -/
def valPostI {I : Type} (Q : I → Val → WProp) : I → Expr → WProp :=
  fun i t ρ => ∃ v : Val, t = .val v ∧ Q i v ρ

/-- W's effectful wp: the least fixed point of "run to a value in `Q` or to a stop `Tb` admits",
written in `Prop` as `ewpTS` is. -/
def ewpW (M : SemWorld) (i : Idx M.Stk) (e : Expr) (Tb : TableI (Idx M.Stk))
    (Q : Idx M.Stk → Val → WProp) : WProp := fun ρ =>
  ∀ P : Idx M.Stk → Expr → WProp,
    (∀ i e ρ, wpGW (ℍ := ℍ) M i e (fun i' t ρ' => valPostI Q i' t ρ' ∨ Tb i' t P ρ') ρ →
      P i e ρ) →
    P i e ρ

/-- A value in `Q`, or a stop owing nothing (`ewpPost`). -/
def ewpPostW {I : Type} (Tb : TableI I) (Q : I → Val → WProp) : I → Expr → WProp :=
  fun i t ρ => valPostI Q i t ρ ∨ Tb i t (fun _ _ _ => False) ρ

/-- The protocol of an operation table at W: `opTable` with `M.share` for `contShare`. -/
def opTabW (M : SemWorld) (T : OpTabI (Idx M.Stk)) : TableI (Idx M.Stk) := fun i t Φ =>
  BoLo.or
    (ex fun K => ex fun n => ex fun j => ex fun v => ex fun en =>
      ⌜t = Kont.plug K (performE (.val (opPayload n j v))) ∧ K.HasHnd n = false ∧
        T n j = some en ∧ en.abort = false⌝ ⋆ (en.PA i v ⋆ M.share T en n i K Φ))
    (ex fun K => ex fun n => ex fun j => ex fun v => ex fun en =>
      ⌜t = Kont.plug K (raiseE (.val (opPayload n j v))) ∧ K.Catches n = false ∧
        T n j = some en ∧ en.abort = true⌝ ⋆
        ((fun ρ => en.PA i v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ))

/-- The error a cancel carries (`errOk`), at any index. -/
def errOkW {I : Type} (T : OpTabI I) (N : List UInt32) (i : I) : Option Val → WProp
  | none => emp
  | some E => ex fun m => ex fun j => ex fun w => ex fun (en : OpEntI I) =>
      ⌜E = opPayload m j w ∧ m ∉ N ∧ T m j = some en ∧ en.abort = true⌝ ⋆
        fun ρ => en.PA i w ρ ∧ NoOwn ρ

/-- The table of a cancel run (`cancelTab`), at any index.  `Cl` is a condition on the index the
cancel ends at (I3.a's closing clause); Core's `cancelTab` is `cancelTabW T N (fun _ => True)`. -/
def cancelTabW {I : Type} (T : OpTabI I) (N : List UInt32) (Cl : I → Prop) : TableI I :=
  fun i t _ =>
  ex fun (K : Kont) => ex fun (err : Option Val) =>
    ⌜t = K.plug (raiseE (.val (cancelVal N err))) ∧ K.Catches 0 = false ∧ Cl i⌝ ⋆
      (errOkW T N i err ⋆ fun ρ => NoOwn ρ)

/-- An operation's entry at W (`OpSig.ent`). -/
def entW (M : SemWorld) (δ : LSub) (o : OpSig) : OpEntI (Idx M.Stk) :=
  ⟨o.q, o.abort, fun i v => M.val true o.A i δ v, fun i v => M.val true o.B i δ v⟩

/-- The table of a row at W (`Row.tab`). -/
def rowTabW (M : SemWorld) (S : Row) (δ : LSub) : OpTabI (Idx M.Stk) :=
  fun n j => (Row.find S n j).map (entW M δ)

/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧` at W (`gSepC`). -/
def gSepW (M : SemWorld) (i : Idx M.Stk) (δ : LSub) : Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ => if s.live then M.val true s.ty i δ v ⋆ gSepW M i δ Γ γ else gSepW M i δ Γ γ

/-- `𝒢⟦Γ⟧` at W (`gDenC`). -/
def gDenW (M : SemWorld) (i : Idx M.Stk) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepW M i δ Γ γ

/-- `Δ; Γ ⊨ e : C` at W at closed rows (`SemC`), at every index. -/
def SemWC (M : SemWorld) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) : Prop :=
  ∀ δ γ (i : Idx M.Stk) ρ, Δ.Models δ → gDenW M i δ Γ γ ρ → M.comp C i δ (substAll γ e) ρ

/-- `Δ; Γ ⊨ e : j` at W at closed rows (`SemJ`): a value judgment is `return V` at `F A`. -/
def SemW₀ (M : SemWorld) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) : Jdg → Prop
  | .comp C => SemWC M Δ Γ e C
  | .val A => SemWC M Δ Γ e (.ret A)

/-- At a row context: every admissible instance. -/
def SemW (M : SemWorld) (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr)
    (j : RowEnv → Jdg) : Prop :=
  ∀ η, Θ.Models η → SemW₀ M Δ (Γ η) e (j η)

/-! ### Core is the σ = [] instance -/

/-- An entry at Core's index read at Core's records. -/
def OpEntI.down (en : OpEntI (Idx Unit)) : OpEnt :=
  ⟨en.q, en.abort, fun ls v => en.PA (ls, ()) v, fun ls v => en.PB (ls, ()) v⟩

/-- A table at Core's index read at Core's records. -/
def OpTabI.down (T : OpTabI (Idx Unit)) : OpTab := fun n i => (T n i).map OpEntI.down

/-- A protocol table at Core's index read at Core's records. -/
def TableI.down (Tb : TableI (Idx Unit)) : Table := fun ls t Φ => Tb (ls, ()) t (fun i e => Φ i.1 e)

/-- **Core's relation as a world whose lend stack has one point.**  Reducible, so that its index
type is `Idx Unit` to every tactic. -/
@[reducible] def coreW : SemWorld where
  Stk := Unit
  nil := ()
  held _ := ([], [])
  Fam fρ ps i := TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1
  Stop a b _ := (∀ p, p ∈ b.1 ↔ p ∈ a.1) ∧ (∀ x, x ∈ b.2.1 ↔ x ∈ a.2.1)
  Ext i i' ρ := Ext i.1 i'.1 ρ
  share T en n i K Φ := contShare (OpTabI.down T) (OpEntI.down en) n i.1 K (fun ls t => Φ (ls, ()) t)
  payStk _ _ := ()
  val b A i δ v := vCE none b A i.1 δ v
  comp C i δ e := cC (ℍ := ℍ) C i.1 δ e

end Targets

end
