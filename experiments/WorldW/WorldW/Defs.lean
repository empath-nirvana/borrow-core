import Core.EffRules
import Core.EffBorrow
import GhostEnd.Table
import GhostEnd.ImmLend
import GhostEnd.Relend
import GhostEnd.Freeze

/-!
# WorldW — the draft definitions (DESIGN §1)

**World of every declaration here: the W-draft `(ρ, ls, σ)`, with the closing obligation `τ` an
index beside it.** These are drafts for the OQ-9 (a) probe. They are not kernel changes; `Core/`
is untouched. A result about them is a result at the W-draft, not at Core's relation (`σ = []`)
and not at Unit 3's `W`.

* `OEnt`: an open entry — a `[TR]` 6.64 frame, a 6.65 lend, a 6.66 anti-frame, a 6.150 reborrow,
  or a handler marker.
* `CloseE`/`ClosePre`/`Close`: each entry's lender exit as resource surgery, innermost first.
* `CompatW`: the σ-component of `#` (6.64's H14 carried by the world).
* `StopW` and `wpGW`: `wpG` (`Core/EffDefs.lean:27-40`) with conjunct (37) read relative to
  `Close`, conjunct (40) (T1) replaced by `StopW`, and the frame quantifier extended.
* `ewpW` and its tables: `ewpTS` at the W-draft.
* `OpenInv`/`OpenInvReb`: the open-entry invariant a continuation holding an entry starts from.
* The table and payload conditions of §1.8.

No `sorry`, `axiom`, `native_decide`, `opaque`, `partial` or `unsafe`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### 1.1 The entries -/

/-- An open entry: a lend open across a stop, or a handler marker. Lists of entries are innermost
first, in context order. -/
inductive OEnt where
  /-- `[TR]` 6.64: an open Imm frame, as `TW.immFrame` recorded it. `r.1 = ⟨ℓ, v, R, T, δ⟩` is in
  `ps`, its lineage is in `rsOf ls`, and `r.2 = α` is its lifetime, the tag of its records. -/
  | imm (r : SRec)
  /-- `[TR]` 6.65: an open Mut lend of the place `l` at the lifetime `α`, its payload read at
  `𝒱⟦T⟧δ`. It has no `ps` record: `TW.mutFold` keeps `ps`. -/
  | mut (l : BoCa.Loc) (α : Life) (T : VTy) (δ : LSub)
  /-- `[TR]` 6.66: an open anti-frame on `l`. The cell `mut(β, v, ρ_P̂, P̂)` is unfolded to
  `own(v) ● ρ_P̂` for the body. The borrower's view was `Mut α 𝒱⟦T⟧δ`, with `α ⊑ β`. -/
  | anti (l : BoCa.Loc) (α β : Life) (T : VTy) (δ : LSub) (P : Val → SPropS BoCa.Loc Val β)
  /-- `[TR]` 6.150: an open reborrow of the view `l ↦ imm(s, w, σR)` at `β`, whose image is
  `χ ∈ reb_β(σR)`. -/
  | reb (l : BoCa.Loc) (s : LSet) (w : Val) (σR : WRes) (hs : σR.InStratum s.join) (β : Life)
      (χ : WRes)
  /-- A handler site of the name `n`, with its extent under OQ-3 (a). The handler lemmas push it
  onto their body's stack. -/
  | hnd (n : UInt32) (h : Option Life)

namespace OEnt

/-- Every kind but a handler marker is a lend. -/
def isLend : OEnt → Bool
  | .hnd .. => false
  | _ => true

def isImm : OEnt → Bool
  | .imm .. => true
  | _ => false

def isMut : OEnt → Bool
  | .mut .. => true
  | _ => false

def isAnti : OEnt → Bool
  | .anti .. => true
  | _ => false

def isReb : OEnt → Bool
  | .reb .. => true
  | _ => false

/-- A `mut` entry at the place `l`. -/
def isMutAt (l : BoCa.Loc) : OEnt → Bool
  | .mut l' _ _ _ => l' == l
  | _ => false

/-- An `anti` entry at the place `m`. -/
def IsAntiAt (m : BoCa.Loc) : OEnt → Prop
  | .anti l _ _ _ _ _ => l = m
  | _ => False

/-- A handler marker of the name `n`. -/
def isHnd (n : UInt32) : OEnt → Bool
  | .hnd n' _ => n' == n
  | _ => false

/-- The entry's lifetime: the frame's tag, the lend's lifetime, the anti view's lifetime, the
reborrow's lifetime; none for a marker. -/
def life? : OEnt → Option Life
  | .imm (_, α) => some α
  | .mut _ α _ _ => some α
  | .anti _ α _ _ _ _ => some α
  | .reb _ _ _ _ _ β _ => some β
  | .hnd .. => none

/-- `life?`, and the extent of a marker under OQ-3 (a): the order D-ORD would read. -/
def ordLife? : OEnt → Option Life
  | .hnd _ h => h
  | e => e.life?

/-- A reborrow's lifetime. -/
def rebLife? : OEnt → Option Life
  | .reb _ _ _ _ _ β _ => some β
  | _ => none

end OEnt

/-- The 6.64 records of `τ`. -/
def immRecs : List OEnt → List FrameRec
  | [] => []
  | .imm (p, _) :: τ => p :: immRecs τ
  | _ :: τ => immRecs τ

/-- `x` is a record of the lineage of the 6.64 entry `e`, tagged at its lifetime. -/
def LinOf : OEnt → SRec → Prop
  | .imm (p, α), x => DescR p x.1 ∧ x.2 = α
  | _, _ => False

/-- `ψ` is an `imm` cell whose lifetime set holds `γ`. -/
def CellU.ImmAt (ψ : CellU BoCa.Loc Val) (γ : Life) : Prop :=
  ∃ s, ψ.lsOf = some s ∧ s.mem γ

/-! ### 1.2 The exits as resource surgery -/

/-- 6.66's refold, without the pin: the unfolded `own(v) ● ρ_P̂` at `l` becomes
`mut(β, v, ρ_P̂, P̂)`, which needs `P̂(v)(ρ_P̂)` (H20–H25, 6.24, 6.28). `ρP` is the split. -/
def CloseEAnti (l : BoCa.Loc) (β : Life) (P : Val → SPropS BoCa.Loc Val β) (ρP π π' : WRes) :
    Prop :=
  ∃ (v : Val) (h : ρP.InStratum β) (hw : P v ⟨ρP, h⟩) (X rest : WRes),
    ResU.CompS (ResU.single l (CellU.ownOf v)) ρP X ∧ ResU.CompS X rest π ∧
    ResU.CompS (ResU.single l (CellU.mutOf β v ρP h P hw)) rest π' ∧ ResU.Valid π'

/-- The pin on an anti step. `ρP` holds no top-level `imm` cell at the lifetime of a `reb` entry
that closes after this step and before the next `mut` entry on `l`. That `mut` entry would unfold
`ρP` back to the top level. -/
def AntiPin (l : BoCa.Loc) (τ : List OEnt) (ρP : WRes) : Prop :=
  ∀ e ∈ τ.takeWhile (fun e => !e.isMutAt l), ∀ β', e.rebLife? = some β' →
    ∀ m ψ, ρP.get m = some ψ → ¬ CellU.ImmAt ψ β'

/-- `π′` is `π` with `e`'s lender exit applied. `τ` lists the entries closed after `e`; only
the anti step reads it. -/
def CloseE (τ : List OEnt) : OEnt → WRes → WRes → Prop
  /- 6.64 (6.38/6.39): the view `imm({α}, v, R)` becomes `ℓ ↦ own(v) ● R`, and the result is
  valid. That is 6.38's G1, `π/ℓ # ρ_v ● ℓ ↦ own(v)`: composition and `✓` of the flattening. -/
  | .imm (p, α), π, π' => ∃ (h : p.R.InStratum (LSet.singleton α).join) (X : WRes),
      π.get p.le = some (CellU.immOf (LSet.singleton α) p.v p.R h) ∧
      ResU.CompS (ResU.single p.le (CellU.ownOf p.v)) p.R X ∧ ResU.CompS (π.del p.le) X π' ∧
      ResU.Valid π'
  /- 6.65 (6.27/6.28): `mut(α, v″, χ, Q̂)` becomes `ℓ ↦ own(v″) ● χ`. -/
  | .mut l α _ _, π, π' => ∃ (v : Val) (χ : WRes) (h : χ.InStratum α)
        (Q : Val → SPropS BoCa.Loc Val α) (hw : Q v ⟨χ, h⟩) (X : WRes),
      π.get l = some (CellU.mutOf α v χ h Q hw) ∧
      ResU.CompS (ResU.single l (CellU.ownOf v)) χ X ∧ ResU.CompS (π.del l) X π' ∧
      ResU.Valid π'
  /- 6.66: the refold, pinned. -/
  | .anti l _ β _ _ P, π, π' => ∃ ρP, AntiPin l τ ρP ∧ CloseEAnti l β P ρP π π'
  /- 6.150 (6.52, 6.59): the image is a reborrow image at `β`, `χ ∈ reb_β(σR)` (H16); its cells
  at `β` are a part of `π` (6.52's split, `ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb`), and they are subtracted,
  `π ⊟ χ∣dom(σR∣mut,own)` (Definition 6.3 as printed, `ResU.SubKeep`). Without the `Le` conjunct
  `⊟` would accept an absent image and subtract nothing. Without the `Reb` conjunct the image's
  cells could sit at lifetimes other than `β`, which the anti step's pin does not cover, and two
  closures of one resource would differ (DESIGN §2, F-CLOSE, correction 2). -/
  | .reb _ _ _ σR _ β χ, π, π' => ResU.Reb β σR χ ∧ ResU.Le (χ.restrictDom σR.exclPart) π ∧
      ResU.SubKeep π (χ.restrictDom σR.exclPart) π' ∧ ResU.Valid π'
  | .hnd _ _, π, π' => π' = π

/-- The first `τ₁.length` steps of closing `τ₁ ++ τ₂`, innermost first. Each step's pin also reads
`τ₂`. -/
inductive ClosePre : List OEnt → List OEnt → WRes → WRes → Prop
  | nil (τ₂ : List OEnt) (π : WRes) : ClosePre [] τ₂ π π
  | cons {e : OEnt} {τ τ₂ : List OEnt} {π π₁ π' : WRes} :
      CloseE (τ ++ τ₂) e π π₁ → ClosePre τ τ₂ π₁ π' → ClosePre (e :: τ) τ₂ π π'

/-- Close the entries innermost first. This is the order the continuation closes them in. -/
abbrev Close (τ : List OEnt) : WRes → WRes → Prop := ClosePre τ []

/-- `ρ` can close `τ` by itself: everything the exits read is in `ρ`. -/
def Holds (τ : List OEnt) (ρ : WRes) : Prop := ∃ ρc, Close τ ρ ρc

/-! ### 1.3 The σ-component of `#` -/

/-- `ρf` is compatible with every closure of `ρ` by `τ`, and inert under it: closing the composite
is closing the part. This is the lender's virtual ownership as a component of `#` at `W`. -/
def CompatW (τ : List OEnt) (ρf ρ : WRes) : Prop :=
  ∀ ρc, Close τ ρ ρc → ResU.Hash ρf ρc ∧
    ∀ X, ResU.CompS ρf ρ X → ∃ Xc, Close τ X Xc ∧ ResU.CompS ρf ρc Xc

/-! ### 1.5 The relativised stop -/

/-- The stop condition at `W`. The run started at `immRecs τ ++ ps`, holding `τ`.
* at a value: nothing stays open; `τ`'s frames leave the frame list and their lineages leave the
  record list (`[TR]` p. 6's `wp`: every frame the run held or opened is closed);
* at any other term: the open 6.64 frames are `immRecs τ′` with the outer ones; the list keeps its
  records except those of `τ`'s closed entries, and gains only `τ′`'s; a 6.64 entry the run opened
  is younger than every record present at both ends; the frame and the leftover are compatible
  with the closure (§1.3). -/
def StopW (τ : List OEnt) (ps ps' : List FrameRec) (ls ls' : List SRec) (t : Expr)
    (τ' : List OEnt) (ρf ρp ρ' π : WRes) : Prop :=
  ((∃ v : Val, t = .val v) →
      τ' = [] ∧ (∀ p, p ∈ ps' ↔ (p ∈ ps ∧ p ∉ immRecs τ)) ∧
      (∀ x, x ∈ ls' ↔ (x ∈ ls ∧ ∀ e ∈ τ, ¬ LinOf e x))) ∧
  ((¬ ∃ v : Val, t = .val v) →
      (∀ p, p ∈ ps' ↔ (p ∈ immRecs τ' ∨ (p ∈ ps ∧ p ∉ immRecs τ))) ∧
      (∀ x, x ∈ ls' ↔ ((x ∈ ls ∧ ∀ e ∈ τ, e ∉ τ' → ¬ LinOf e x) ∨ ∃ e ∈ τ', LinOf e x)) ∧
      (∀ q, OEnt.imm q ∈ τ' → OEnt.imm q ∉ τ → ∀ x ∈ ls, x ∈ ls' → q.2 ⊏ x.2) ∧
      CompatW τ' ρf π ∧ CompatW τ' ρp ρ')

/-- `wpG` for a run that holds the obligation `τ` under `σ`. -/
def wpGW (τ σ : List OEnt) (ls : List SRec) (e : Expr)
    (Q : List OEnt → List SRec → Expr → WProp) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → CompatW τ ρf ρ →
    ResU.CompS ρf ρ fρ → TW fρ (immRecs τ ++ ps) (rsOf ls) → Tagged fρ (immRecs τ ++ ps) ls →
    (∀ p ∈ immRecs σ, p ∈ ps) →
    ∀ (A : Alloc) (k : Nat),
    ∃ (ρ' ρp fρ' fρ'p π ρc πc : WRes) (t : Expr) (μ μ' : Heap) (ps' : List FrameRec)
      (ls' : List SRec) (τ' : List OEnt),
      ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.Lower fρ μ ∧ ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      (∃ k', ARun A k μ e k' μ' t) ∧
      ResU.CompS ρ' ρp π ∧ Close τ ρ ρc ∧ Close τ' π πc ∧ ResU.UpdV ρc πc ∧
      NoOwn ρp ∧ TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
      StopW τ ps ps' ls ls' t τ' ρf ρp ρ' π ∧ Q τ' ls' t ρ'

/-! ### 1.6 Tables and `ewp` at `W` -/

/-- A continuation: `Φ τ σ ls e`, the run of `e` holding `τ` under `σ`. -/
abbrev ContW := List OEnt → List OEnt → List SRec → Expr → WProp

/-- A table: the stopped run's stack, the list, the entries `τ′` the stop left open, the stopped
term, and the continuations owed. -/
abbrev TableW := List OEnt → List SRec → List OEnt → Expr → ContW → WProp

def ewpStepW (Tb : TableW) (Q : List SRec → Val → WProp) (P : ContW) : ContW :=
  fun τ σ ls e => wpGW τ σ ls e (fun τ' ls' t ρ =>
    (∃ v : Val, t = .val v ∧ τ' = [] ∧ Q ls' v ρ) ∨ Tb σ ls' τ' t P ρ)

/-- The least fixed point, in `Prop`, as `ewpTS` (`Core/EffDefs.lean:73`). -/
def ewpW (τ σ : List OEnt) (ls : List SRec) (e : Expr) (Tb : TableW)
    (Q : List SRec → Val → WProp) : WProp := fun ρ =>
  ∀ P : ContW, (∀ τ σ ls e ρ, ewpStepW Tb Q P τ σ ls e ρ → P τ σ ls e ρ) → P τ σ ls e ρ

/-- A cancel run ends at the cancel with nothing open. -/
def cancelTabW (T : OpTab) (N : List UInt32) : TableW := fun _ ls τ' t _ ρ =>
  τ' = [] ∧ cancelTab T N ls t (fun _ _ _ => False) ρ

/-- `Table.withFr` at `W`: the stop also hands back the frame `Fr`. -/
def withOwnerW (Tb : TableW) (Fr : List SRec → WProp) : TableW :=
  fun σ ls τ' t Φ => Tb σ ls τ' t Φ ⋆ Fr ls

def owedW (Tc : List UInt32 → TableW) (n : UInt32) (σ : List OEnt) (ls : List SRec)
    (τ : List OEnt) (K : Kont) : WProp := fun ρ =>
  ∀ N : List UInt32, n ∈ N → (∀ m ∈ K.hndNames, m ∈ N) →
    ewpW τ σ ls (K.plug (raiseE (.val (cancelVal N none)))) (Tc N) (fun _ _ _ => False) ρ

def shareW (Tc : List UInt32 → TableW) (en : OpEnt) (n : UInt32) (σ : List OEnt)
    (ls : List SRec) (τ' : List OEnt) (K : Kont) (Φ : ContW) : WProp := fun ρ =>
  (en.q = .unr → ρ = PMap.empty ∧ τ' = []) ∧                       -- assumption, owned by batch 3
  ∀ ls', Ext ls ls' ρ →
    (∀ w : Val, (en.PB ls' w ─⋆ Φ τ' σ ls' (K.plug (.val w))) ρ) ∧
    (en.q ≠ .lin → owedW Tc n σ ls' τ' K ρ)

/-- The protocol table of `T` at `W`. A stop that closes the entry hands back the frame `Fr`.
`Fr` is `emp` for a borrower's own table, and the lender's place in a frame lemma's
conclusion. -/
def opTabW (T : OpTab) (Fr : List SRec → WProp) : TableW := fun σ ls τ' t Φ =>
  BoLo.or
    (ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
      ex fun (en : OpEnt) =>
        ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
          T n i = some en ∧ en.abort = false⌝ ⋆
        fun ρ => ∃ ρa ρk, ResU.CompS ρa ρk ρ ∧ en.PA ls v ρa ∧
          shareW (fun N => withOwnerW (cancelTabW T N) Fr) en n σ ls τ' K Φ ρk ∧
          Holds τ' ρk ∧ CompatW τ' ρa ρk)
    (ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
      ex fun (en : OpEnt) =>
        ⌜t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
          T n i = some en ∧ en.abort = true ∧ τ' = []⌝ ⋆
          (((fun ρ => en.PA ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ) ⋆ Fr ls))

abbrev opTableW (T : OpTab) : TableW := opTabW T (fun _ => emp)

/-- OQ-3 (a): the table of a handled body at the handler's extent `h`. Every lend a stop hands to
the handler was opened below `h`: an `anti` entry opens no lifetime, and may unfold a view from
outside. The stop's resource is in `Res_h` once the entries are closed. That is 6.147 read
relative to `Close`; GhostEnd's `wpG_box`/`frozen_above_extent` are its form at today's stop. -/
def extTabW (h : Life) (Tb : TableW) : TableW := fun σ ls τ' t Φ ρ =>
  (∀ e ∈ τ', e.isAnti = false → ∀ β, e.life? = some β → β ⊏ h) ∧
  (∀ ρc, Close τ' ρ ρc → ρc.InStratum h) ∧ Tb σ ls τ' t Φ ρ

/-- The relation of `κ` at an operation's entry. `κ` holds `τ`. It may be called under any
extension of the handler's stack, at every extension of the list, when the re-entry condition
`re` holds at the call. `re` is `fun _ _ _ => True` without a handler extent (OQ-3 (b)), and
`ExtentOK h τ` when the reinstalled handler re-enters at the extent `h` (OQ-3 (a), §3.4). -/
def KapRelW (Tout : OpTab) (Qout : List SRec → Val → WProp) (en : OpEnt)
    (re : List OEnt → List SRec → WRes → Prop) (σ : List OEnt) (ls : List SRec)
    (τ : List OEnt) (κ : Val) : WProp := fun ρ =>
  (en.q = .unr → ρ = PMap.empty ∧ τ = []) ∧                         -- assumption, owned by batch 3
  ∀ (extra : List OEnt) (ls' : List SRec), Ext ls ls' ρ →
    (∀ w : Val, (en.PB ls' w ─⋆ fun ρ' => re (extra ++ σ) ls' ρ' →
      ewpW τ (extra ++ σ) ls' (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w))
        (opTableW Tout) Qout ρ') ρ) ∧
    (en.q ≠ .lin → re (extra ++ σ) ls' ρ →
      ewpW τ (extra ++ σ) ls' (.app κ.1 (.val (Val.inj₂ .unit))) (opTableW Tout)
        (fun _ v => ⌜v = Val.unit⌝) ρ)

abbrev KapRelWB (Tout : OpTab) (Qout : List SRec → Val → WProp) (en : OpEnt) :=
  KapRelW Tout Qout en (fun _ _ _ => True)

/-! ### 1.7 The open-entry invariant -/

/-- `e` is open over `ρ`, and the continuation also holds its inner entries `τi`. -/
def OpenInv (τi : List OEnt) (ls : List SRec) : OEnt → WRes → Prop
  /- 6.64: after closing `τi`, `ρ` agrees with the lend table at `(p.le, α)` (`GhostEnd.TabAt`:
  every borrow cell `⊒ α`, every one off `p.le` strictly above). The exit is defined (G1), and the
  payload is in `𝒱⟦T⟧` at the current list. -/
  | .imm (p, α), ρ => ∃ ρi ρe, ClosePre τi [.imm (p, α)] ρ ρi ∧ GhostEnd.TabAt p.le α ρi ∧
      CloseE [] (.imm (p, α)) ρi ρe ∧ vC true p.T ls p.δ p.v p.R
  /- 6.65: after closing `τi`, `ρ` holds the lend's own cell `mut(α, …)` at `l` as `ptoMutS`
  reads it at the current list, and the rest is strictly above `α`. -/
  | .mut l α T δ, ρ => ∃ ρi ρv ρr, ClosePre τi [.mut l α T δ] ρ ρi ∧ ResU.CompS ρv ρr ρi ∧
      ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ρv ∧
      (∃ v χ h Q hw, ρv = ResU.single l (CellU.mutOf α v χ h Q hw)) ∧ ρr.InStratum α
  /- 6.66: after closing `τi`, refolding at `l` gives back the borrower's view
  `ℓ ↦ Mut α 𝒱⟦T⟧δ` as `ptoMutS` reads it at the current list. -/
  | .anti l α β T δ P, ρ => ∃ ρi ρm ρv ρr, ClosePre τi [.anti l α β T δ P] ρ ρi ∧
      CloseE [] (.anti l α β T δ P) ρi ρm ∧
      ResU.CompS ρv ρr ρm ∧ ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ρv ∧
      ∃ v χ h hw, ρv = ResU.single l (CellU.mutOf β v χ h P hw)
  | .reb .., _ => False      -- 6.150's view sits beside the borrower: `OpenInvReb`
  | .hnd .., _ => True

/-- 6.150: the continuation holds the view `ρ_i = l ↦ imm(s, w, σR)` beside `X`, the borrower's
resource. After closing `τi` (with the reborrow still to close), `X` holds the image:
* `χ ∈ reb_β(σR)` (H16);
* subtracting the image's cells at `β` (Definition 6.3's `⊟`) leaves `Xr`, of which the image is
  the rest (6.52's split at the entry);
* `Xr` is strictly above `β` (H15, and 6.52's `@(ρ⁺ ⊟ ρ_reb) ⊐ β`);
* `X` is compatible with the view (H18–H20, 6.55). -/
def OpenInvReb (τi : List OEnt) (l : BoCa.Loc) (s : LSet) (w : Val) (σR : WRes)
    (hs : σR.InStratum s.join) (β : Life) (χ : WRes) (X : WRes) : Prop :=
  ResU.Reb β σR χ ∧
  ∃ Xc Xr, ClosePre τi [.reb l s w σR hs β χ] X Xc ∧
    ResU.SubKeep Xc (χ.restrictDom σR.exclPart) Xr ∧
    ResU.CompS Xr (χ.restrictDom σR.exclPart) Xc ∧
    Xr.InStratum β ∧
    ResU.Hash (ResU.single l (CellU.immOf s w σR hs)) Xc

/-! ### 1.8 Table and payload conditions -/

/-- R-CLOSEDOP (OQ-56 (a)): arguments and answers own every cell they hold and borrow none
(D-TABLEOK (3)–(4)). -/
def ClosedOps (T : OpTab) : Prop :=
  ∀ n i en, T n i = some en → ∀ ls v ρ (α : Life),
    (en.PA ls v ρ → ρ.InStratum α) ∧ (en.PB ls v ρ → ρ.InStratum α)

/-- No operation's continuation is unrestricted: batch 3 decides whether such a continuation may
hold an entry (§1.6). -/
def NoUnr (T : OpTab) : Prop := ∀ n i en, T n i = some en → en.q ≠ .unr

/-- The operations of `n` resume, at the qualifier `q`. -/
def OpAt (T : OpTab) (n : UInt32) (q : Qual) : Prop :=
  ∀ i en, T n i = some en → en.abort = false ∧ en.q = q

/-- The lifetime order the pin assumes (§1.2): a `reb` entry closed after an `anti` entry, before
the next `mut` entry on the anti's place, is below the anti's cell lifetime. -/
def OblWf (τ : List OEnt) : Prop :=
  ∀ i (hi : i < τ.length) l α β T δ P, τ[i] = .anti l α β T δ P →
    ∀ e ∈ (τ.drop (i + 1)).takeWhile (fun e => !e.isMutAt l), ∀ β', e.rebLife? = some β' →
      β' ⊏ β

/-- The 6.64 entries of `τ` are younger than `α`: a borrower's own entries, opened inside a lend
at `α`. Not the case for an entry the borrower holds through a continuation it resumes (§3.4). -/
def YoungerThan (τ : List OEnt) (α : Life) : Prop := ∀ q, OEnt.imm q ∈ τ → q.2 ⊏ α

/-- The payload's relation does not read the record list. -/
def ListStable (T : VTy) (δ : LSub) : Prop :=
  ∀ ls ls' w ρ, vC true T ls δ w ρ ↔ vC true T ls' δ w ρ

def exitI (p : FrameRec) (α : Life) (Q : List SRec → Val → WProp) : List SRec → Val → WProp :=
  fun ls v => box α (ptoOwn p.le p.v ─⋆ (vC true p.T ls p.δ p.v ─⋆ Q ls v))

def exitM (l : BoCa.Loc) (α : Life) (T : VTy) (δ : LSub) (Q : List SRec → Val → WProp) :
    List SRec → Val → WProp :=
  fun ls v => box α (all fun w => ptoOwn l w ─⋆ (vC true T ls δ w ─⋆ Q ls v))

/-- 6.66's postcondition: the content handed back, then the view taken. -/
def antiPost (l : BoCa.Loc) (α : Life) (T : VTy) (δ : LSub) (Q : List SRec → Val → WProp) :
    List SRec → Val → WProp :=
  fun ls v => ex fun w => ptoOwn l w ⋆ vC true T ls δ w ⋆
    (ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ─⋆ Q ls v)

def viewM (l : BoCa.Loc) (α : Life) (T : VTy) (δ : LSub) : List SRec → WProp :=
  fun ls => ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ)

/-- Core's added hypothesis `hQ` of 6.64 (`Core/FrameRules.lean:60`): `Q` is carried along `Ext`.
It is not printed. -/
def QExt (Q : List SRec → Val → WProp) : Prop :=
  ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q ls₁ w ρ → Q ls₂ w ρ

end WorldW

end
