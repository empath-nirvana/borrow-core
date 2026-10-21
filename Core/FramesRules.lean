import Core.FramesDefs

/-!
# Core — frames: the frame judgment  `[spec §47]`

`FDerives Δ Γ Φ Π Πn Πx e Σ E A` reads: `e` is the elaboration of a frame that takes the slots
in the states `Π` and hands them back in the states `Πn` at its normal exit and `Πx` at every
local exit, at the row `Σ`, with the exit row `E` and the normal answer `A`, in the Core context
`Γ` and the block environment `Φ`. The elaborated Core term is an index: the judgment is a closed
set of derived rules, packaged as an inductive so that a property of every frame is one induction
(`Core/FramesTheorems.lean`). It adds nothing to `CDerives`, `VTy`, `CTy` or the relation.

**The exit row and the slots' states of each rule, from its premises.** `E` is to local exits
what `Σ` is to effects; the states are threaded as a type is through a sequence:

| rule | exit row | slots: in → normal / exits |
|---|---|---|
| `core`, `use`, `callBlock` | any `E` | unchanged (a block by its own type) |
| `exit k` | any `E` with `E[k] = (l, B)`: the `[perform]` of exits | the exits' state is the state there |
| `bind` | the premises' `E` | `M`'s normal state is `N`'s entry; both exit at the same state |
| `case` | the premises' `E` | both arms the same |
| `catch` | the premise's row minus its head: the `[handle]` of exits | the handler runs from the exits' state |
| `under`, `lend`, `new` | the premises' `E` | the head slot added to every state (`new`: removed, its cell released at the normal exit, destroyed at the others) |
| `swap` | any `E` | the head cell `Ref A` becomes `Ref B` |
| `caseSlot` | the premises' `E` | the head slot `P ⊕ Q` read as `P` and as `Q`, the same cell |
| `widen` | the premise's `E` | each exit's state widened into states with tags |
| `loopCount`, `loopIter` | the turn's row minus its head (the loop's `break`) | the turn keeps the state; the source's end widened into the exits' |
| `sub` | the premise's `E` | unchanged |

Raise and abort are not exits of `E`: they are operations of `Σ`, and every rule that runs Core
code while holding slots holds them under a `[then]` finaliser or lends them by an unwinding
borrow constant (§19).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Frames
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A frame-typed block of the program: a closed value `v : !U(B ⊸ Fr Σ Π Πn Πx E A)` (a
top-level frame definition; a local closure that writes places is lambda-lifted to one, since it
captures only places and persistent values). -/
structure FBlock where
  v : Val
  B : VTy
  S : Row
  P : List VTy
  Pn : List VTy
  X : List VTy
  E : ExitRow
  A : VTy

/-- The block is a closed `λ`, typed at its frame type. -/
def FBlock.Wf (Δ : LifeCtx) (b : FBlock) : Prop :=
  closedAt 0 b.v.1 = true ∧ (∃ body, b.v = Val.lam body) ∧
    CDerives Δ [] (.val b.v) (.val (blockTy b.B b.S b.P b.Pn b.X b.E b.A))

/-- The side conditions of the unwinding borrow constant at a source, for a fresh `'x`. -/
def LendOk (Δ : LifeCtx) (x : LifeVar) : LendSrc → Prop
  | .ref A => ¬ VFree x A ∧ ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A
  | .mut _ A => ¬ VFree x A

/-- **The frame judgment.** -/
inductive FDerives : LifeCtx → Ctx VTy → List FBlock → List VTy → List VTy → List VTy → Expr →
    Row → ExitRow → VTy → Prop where
  /-- A Core computation, run while the frame holds its slots; its answer is the normal exit. -/
  | core {Δ Γ Φ Ps X N S E A} (hS : FRow S) (hP : SlotsOk Ps)
      (hN : CDerives Δ Γ N (.comp (CTy.effOf S A))) :
      FDerives Δ Γ Φ Ps Ps X (coreE Ps N) S E A
  /-- Leave by the `k`-th exit, the slots as they are. -/
  | exit {Δ Γ Φ Ps Pn V S E A} {k l : Nat} {B : VTy} (hk : E[k]? = some (l, B))
      (hV : CDerives Δ Γ V (.val B)) :
      FDerives Δ Γ Φ Ps Pn Ps (exitE k V) S E A
  /-- Sequence: `M`'s normal state is `N`'s entry; an exit of `M` skips `N`. -/
  | bind {Δ Γ Γ₁ Γ₂ Φ P₀ P₁ P₂ X eM eN S E A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂)
      (hX : E = [] ∨ CtxDtor Γ₂)
      (hM : FDerives Δ Γ₁ Φ P₀ P₁ X eM S E A)
      (hN : FDerives Δ (⟨A, true⟩ :: Γ₂) Φ P₁ P₂ X eN S E B) :
      FDerives Δ Γ Φ P₀ P₂ X (bindE E Γ₂ eM eN) S E B
  /-- A case whose arms are frames over the same slots: the join is the frame's. -/
  | case {Δ Γ Γs Γb Φ P Pn X V e₁ e₂ S E A B C} (hs : Ctx.SplitP Γ Γs Γb)
      (hV : CDerives Δ Γs V (.val (.sum A B)))
      (h₁ : FDerives Δ (⟨A, true⟩ :: Γb) Φ P Pn X e₁ S E C)
      (h₂ : FDerives Δ (⟨B, true⟩ :: Γb) Φ P Pn X e₂ S E C) :
      FDerives Δ Γ Φ P Pn X (caseE V e₁ e₂) S E C
  /-- Catch the head exit (a labelled block's exit, the function's `return`, a turn's
  `continue`); the handler runs from the exits' state. -/
  | catch {Δ Γ Γ₁ Γ₂ Φ P Pn X eM eH S E A} {l : Nat} {B : VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂) (hX : CtxDtor Γ₂)
      (hM : FDerives Δ Γ₁ Φ P Pn X eM S ((l, B) :: E) A)
      (hH : FDerives Δ (⟨B, true⟩ :: Γ₂) Φ X Pn X eH S E A) :
      FDerives Δ Γ Φ P Pn X (catchE Γ₂ eM eH) S E A
  /-- A frame over `Π` inside a frame over `Q :: Π`. -/
  | under {Δ Γ Φ P Pn X eM S E A} {Q : VTy} (hS : FRow S) (hQ : SlotOk Q)
      (hM : FDerives Δ Γ Φ P Pn X eM S E A) :
      FDerives Δ Γ Φ (Q :: P) (Q :: Pn) (Q :: X) (underE Q eM) S E A
  /-- Lend the head slot to a Core callback (a statement that reads or writes the place). -/
  | use {Δ Γ Φ Ps X N S E B} (src : LendSrc) (x : LifeVar) (hx : Δ.find? x = none)
      (hS : S.Unwind x) (hS' : FRow S) (hP : SlotsOk Ps) (hsrc : LendOk Δ x src)
      (hsrcD : SlotOk src.ty) (hB : ¬ VFree x B)
      (hN : CDerives Δ Γ N (.val (cbUTy x Δ.meetOfDom (.mut (.var x) src.payload) B S))) :
      FDerives Δ Γ Φ (src.ty :: Ps) (src.ty :: Ps) X (useE src Ps N) S E B
  /-- Reborrow the head slot at a fresh `'x` for a frame over `Mut 'x A :: Π`: a borrow block
  whose body is a frame, with its exits passed out of the lend. -/
  | lend {Δ Γ Φ P Pn X eM S E A} (src : LendSrc) (x : LifeVar) (hΔ : Δ.Ok) (hx : Δ.find? x = none)
      (hS : S.Unwind x) (hsrc : LendOk Δ x src) (hsrcD : SlotOk src.ty)
      (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) (hfreeP : ¬ VFree x (slotsTy P))
      (hfree : ¬ VFree x (ansTy Pn X A E))
      (hout : VOutlives (Δ.extend x Δ.meetOfDom) (.var x) (slotsTy Pn) ∧
        VOutlives (Δ.extend x Δ.meetOfDom) (.var x) A ∧
        VOutlives (Δ.extend x Δ.meetOfDom) (.var x) (slotsTy X) ∧
        VOutlives (Δ.extend x Δ.meetOfDom) (.var x) E.sumTy)
      (hM : FDerives (Δ.extend x Δ.meetOfDom) Γ Φ (.mut (.var x) src.payload :: P)
        (.mut (.var x) src.payload :: Pn) (.mut (.var x) src.payload :: X) eM S E A) :
      FDerives Δ Γ Φ (src.ty :: P) (src.ty :: Pn) (src.ty :: X) (lendE src eM) S E A
  /-- `let mut`: a new slot for `M`; at the normal exit the cell, in the state `q`, is released
  and its content handed out; at the others, in the state `Q'`, destroyed. -/
  | new {Δ Γ Γ₁ Γ₂ Φ P Pn X V eM S E B} {A Q' : VTy} {q : CellSt} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hA : HasDtor A) (hq : q.Ok) (hQ' : SlotOk Q')
      (hV : CDerives Δ Γ₁ V (.val A))
      (hM : FDerives Δ Γ₂ Φ (.ref A :: P) (q.ty :: Pn) (Q' :: X) eM S E B) :
      FDerives Δ Γ Φ P Pn X (newE q Q' V eM) S E (.tensor B q.content)
  /-- Strong update of the head cell: `swap c V`, the old content the answer. A move out is
  `V = ()`, a put back `V = a`. -/
  | swap {Δ Γ Φ Ps X V S E} {A B : VTy} (hB : HasDtor B) (hV : CDerives Δ Γ V (.val B)) :
      FDerives Δ Γ Φ (.ref A :: Ps) (.ref B :: Ps) X (swapSE V) S E A
  /-- The case on the head slot's tag: one frame per state, the same cell in both. -/
  | caseSlot {Δ Γ Φ Ps Pn X e₁ e₂ S E A} {P₁ P₂ : VTy}
      (h₁ : FDerives Δ Γ Φ (P₁ :: Ps) Pn X e₁ S E A)
      (h₂ : FDerives Δ Γ Φ (P₂ :: Ps) Pn X e₂ S E A) :
      FDerives Δ Γ Φ (.sum P₁ P₂ :: Ps) Pn X (caseSlotE e₁ e₂) S E A
  /-- Widen the slots' states at the normal exit and at the exits into states with tags: the
  join of two arms whose states differ. -/
  | widen {Δ Γ Φ P Pn Pn' X X' e S E A} {ws wx : List WStep} (hn : Widens ws Pn Pn')
      (hx : Widens wx X X') (h : FDerives Δ Γ Φ P Pn X e S E A) :
      FDerives Δ Γ Φ P Pn' X' (widenE ws wx e) S E A
  /-- The counted loop with an exit, at the pure row: the head exit of the turn's row is the
  loop's `break`. The turn keeps the slots' state; the loop's answer is its last state (the
  source ended, the slots widened into the exits' state) or `break`'s payload. -/
  | loopCount {Δ Γ Γ₁ Γn Γs Γ₂ Φ P X n s₀ eM E} {ws : List WStep} {l : Nat} {S₀ B : VTy}
      (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γn Γs) (hp : Persistent Γ₂)
      (hw : Widens ws P X)
      (hn : CDerives Δ Γn n (.val (.int .w32))) (hs0 : CDerives Δ Γs s₀ (.val S₀))
      (hM : FDerives Δ (⟨S₀, true⟩ :: ⟨.int .w32, true⟩ :: Γ₂) Φ P P X eM [] ((l, B) :: E) S₀) :
      FDerives Δ Γ Φ P X X (loopCountE ws n s₀ eM) [] E (.sum S₀ B)
  /-- The div loop, at a row holding `Div`: the turn's head exit is its `break`; the loop's
  answer is `break`'s payload, or `()` when `Div`'s handler closes it (the slots widened into the
  exits' state). -/
  | loopIter {Δ Γ Γ₁ Γ₂ Φ P X s₀ eM S E} {ws : List WStep} {l : Nat} {S₀ B : VTy}
      (hdiv : Row.divB S = true) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hp : Persistent Γ₂)
      (hw : Widens ws P X)
      (hS₀ : HasDtor S₀) (hs0 : CDerives Δ Γ₁ s₀ (.val S₀))
      (hM : FDerives Δ (⟨S₀, true⟩ :: Γ₂) Φ P P X eM S ((l, B) :: E) S₀) :
      FDerives Δ Γ Φ P X X (loopIterE ws S₀ s₀ eM) S E (.sum B .unit)
  /-- Call a block of the program on a variable, with the current slots. The block is typed at
  the call's lifetime context: under a `lend` that is the extended one, and a typing at the
  program's context does not transfer (the borrow constants' types read `⊓Δ`). -/
  | callBlock {Δ Γ Φ j} {b : FBlock} {k : Nat} (hk : Φ[k]? = some b) (hb : b.Wf Δ)
      (hj : Ctx.SoloP Γ j b.B) :
      FDerives Δ Γ Φ b.P b.Pn b.X (callE b.v j) b.S b.E b.A
  /-- Row weakening. -/
  | sub {Δ Γ Φ P Pn X e S S' E A} (hle : RowLe S S') (h : FDerives Δ Γ Φ P Pn X e S E A) :
      FDerives Δ Γ Φ P Pn X (subE e) S' E A

end BoCa.Fig16.LogRel.Core.Frames

end
