import Frames.Defs

/-!
# Frames — the frame judgment

`FDerives Δ Γ Φ Π e Σ E A` reads: `e` is the elaboration of a frame over the slots `Π`, at the
row `Σ`, with the exit row `E` and the normal answer `A`, in the Core context `Γ` and the block
environment `Φ`. As `Affine`'s `ADerives`, the elaborated Core term is an index: the judgment is
a closed set of derived rules, packaged as an inductive so that a property of every frame is one
induction (`Theorems.lean`). It adds nothing to `CDerives`, `VTy`, `CTy` or the relation.

**The exit row of each rule, from its premises.** `E` is to local exits what `Σ` is to effects:

| rule | exit row of the conclusion |
|---|---|
| `core`, `use`, `callBlock` | any `E` (Core code leaves by no local exit; a block by its own row) |
| `exit k` | any `E` with `E[k] = (l, B)`: the `[perform]` of exits |
| `bind`, `case`, `under`, `new`, `sub` | the premises' `E`, unchanged |
| `catch` | the premise's row minus its head: the `[handle]` of exits |
| `loopCount`, `loopIter` | the turn's row minus its head (the loop's `break`) |
| `lend` | the premise's `E`, passed out of the lend in the callback's boxed answer |

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

/-- A frame-typed block of the program: a closed value `v : !U(B ⊸ Fr Σ Π E A)` (a top-level
frame definition; a local closure that writes places is lambda-lifted to one, since it captures
only places and persistent values). -/
structure FBlock where
  v : Val
  B : VTy
  S : Row
  Ps : List VTy
  E : ExitRow
  A : VTy

/-- The block is a closed `λ`, typed at its frame type. -/
def FBlock.Wf (Δ : LifeCtx) (b : FBlock) : Prop :=
  closedAt 0 b.v.1 = true ∧ (∃ body, b.v = Val.lam body) ∧
    CDerives Δ [] (.val b.v) (.val (blockTy b.B b.S b.Ps b.E b.A))

/-- The side conditions of the unwinding borrow constant at a source, for a fresh `'x`. -/
def LendOk (Δ : LifeCtx) (x : LifeVar) : LendSrc → Prop
  | .ref A => ¬ VFree x A ∧ ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A
  | .mut _ A => ¬ VFree x A

/-- **The frame judgment.** -/
inductive FDerives : LifeCtx → Ctx VTy → List FBlock → List VTy → Expr → Row → ExitRow → VTy →
    Prop where
  /-- A Core computation, run while the frame holds its slots; its answer is the normal exit. -/
  | core {Δ Γ Φ Ps N S E A} (hS : FRow S) (hP : SlotsOk Ps)
      (hN : CDerives Δ Γ N (.comp (CTy.effOf S A))) :
      FDerives Δ Γ Φ Ps (coreE Ps N) S E A
  /-- Leave by the `k`-th exit. -/
  | exit {Δ Γ Φ Ps V S E A} {k l : Nat} {B : VTy} (hk : E[k]? = some (l, B))
      (hV : CDerives Δ Γ V (.val B)) :
      FDerives Δ Γ Φ Ps (exitE k V) S E A
  /-- Sequence: an exit of `M` skips `N`. -/
  | bind {Δ Γ Γ₁ Γ₂ Φ Ps eM eN S E A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂)
      (hX : E = [] ∨ CtxDtor Γ₂)
      (hM : FDerives Δ Γ₁ Φ Ps eM S E A)
      (hN : FDerives Δ (⟨A, true⟩ :: Γ₂) Φ Ps eN S E B) :
      FDerives Δ Γ Φ Ps (bindE E Γ₂ eM eN) S E B
  /-- A case whose arms are frames over the same slots: the join is the frame's. -/
  | case {Δ Γ Γs Γb Φ Ps V e₁ e₂ S E A B C} (hs : Ctx.SplitP Γ Γs Γb)
      (hV : CDerives Δ Γs V (.val (.sum A B)))
      (h₁ : FDerives Δ (⟨A, true⟩ :: Γb) Φ Ps e₁ S E C)
      (h₂ : FDerives Δ (⟨B, true⟩ :: Γb) Φ Ps e₂ S E C) :
      FDerives Δ Γ Φ Ps (caseE V e₁ e₂) S E C
  /-- Catch the head exit (a labelled block's exit, the function's `return`, a turn's
  `continue`). -/
  | catch {Δ Γ Γ₁ Γ₂ Φ Ps eM eH S E A} {l : Nat} {B : VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂) (hX : CtxDtor Γ₂)
      (hM : FDerives Δ Γ₁ Φ Ps eM S ((l, B) :: E) A)
      (hH : FDerives Δ (⟨B, true⟩ :: Γ₂) Φ Ps eH S E A) :
      FDerives Δ Γ Φ Ps (catchE Γ₂ eM eH) S E A
  /-- A frame over `Π` inside a frame over `Q :: Π`. -/
  | under {Δ Γ Φ Ps eM S E A} {Q : VTy} (hS : FRow S) (hQ : SlotOk Q)
      (hM : FDerives Δ Γ Φ Ps eM S E A) :
      FDerives Δ Γ Φ (Q :: Ps) (underE Q eM) S E A
  /-- Lend the head slot to a Core callback (a statement that reads or writes the place). -/
  | use {Δ Γ Φ Ps N S E B} (src : LendSrc) (x : LifeVar) (hx : Δ.find? x = none)
      (hS : S.Unwind x) (hS' : FRow S) (hP : SlotsOk Ps) (hsrc : LendOk Δ x src)
      (hsrcD : SlotOk src.ty) (hB : ¬ VFree x B)
      (hN : CDerives Δ Γ N (.val (cbUTy x Δ.meetOfDom (.mut (.var x) src.payload) B S))) :
      FDerives Δ Γ Φ (src.ty :: Ps) (useE src Ps N) S E B
  /-- Reborrow the head slot at a fresh `'x` for a frame over `Mut 'x A :: Π`: a borrow block
  whose body is a frame, with its exits passed out of the lend. -/
  | lend {Δ Γ Φ Ps eM S E A} (src : LendSrc) (x : LifeVar) (hΔ : Δ.Ok) (hx : Δ.find? x = none)
      (hS : S.Unwind x) (hsrc : LendOk Δ x src) (hsrcD : SlotOk src.ty)
      (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
      (hfree : ¬ VFree x (.tensor (slotsTy Ps) (exitsTy A E)))
      (hout : VOutlives (Δ.extend x Δ.meetOfDom) (.var x) (slotsTy Ps) ∧
        VOutlives (Δ.extend x Δ.meetOfDom) (.var x) (exitsTy A E))
      (hM : FDerives (Δ.extend x Δ.meetOfDom) Γ Φ (.mut (.var x) src.payload :: Ps) eM S E A) :
      FDerives Δ Γ Φ (src.ty :: Ps) (lendE src eM) S E A
  /-- `let mut`: a new slot for `M`; its last content is handed out at the normal exit. -/
  | new {Δ Γ Γ₁ Γ₂ Φ Ps V eM S E B} {A : VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hA : HasDtor A)
      (hV : CDerives Δ Γ₁ V (.val A))
      (hM : FDerives Δ Γ₂ Φ (.ref A :: Ps) eM S E B) :
      FDerives Δ Γ Φ Ps (newE A V eM) S E (.tensor B A)
  /-- The counted loop with an exit, at the pure row: the head exit of the turn's row is the
  loop's `break`. The loop's answer is its last state (the source ended) or `break`'s payload. -/
  | loopCount {Δ Γ Γ₁ Γn Γs Γ₂ Φ Ps n s₀ eM E} {l : Nat} {S₀ B : VTy}
      (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γn Γs) (hp : Persistent Γ₂)
      (hn : CDerives Δ Γn n (.val (.int .w32))) (hs0 : CDerives Δ Γs s₀ (.val S₀))
      (hM : FDerives Δ (⟨S₀, true⟩ :: ⟨.int .w32, true⟩ :: Γ₂) Φ Ps eM [] ((l, B) :: E) S₀) :
      FDerives Δ Γ Φ Ps (loopCountE n s₀ eM) [] E (.sum S₀ B)
  /-- The div loop, at a row holding `Div`: the turn's head exit is its `break`; the loop's
  answer is `break`'s payload, or `()` when `Div`'s handler closes it. -/
  | loopIter {Δ Γ Γ₁ Γ₂ Φ Ps s₀ eM S E} {l : Nat} {S₀ B : VTy}
      (hdiv : Row.divB S = true) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hp : Persistent Γ₂)
      (hS₀ : HasDtor S₀) (hs0 : CDerives Δ Γ₁ s₀ (.val S₀))
      (hM : FDerives Δ (⟨S₀, true⟩ :: Γ₂) Φ Ps eM S ((l, B) :: E) S₀) :
      FDerives Δ Γ Φ Ps (loopIterE S₀ s₀ eM) S E (.sum B .unit)
  /-- Call a block of the program on a variable, with the current slots. The block is typed at
  the call's lifetime context: under a `lend` that is the extended one, and a typing at the
  program's context does not transfer (the borrow constants' types read `⊓Δ`). -/
  | callBlock {Δ Γ Φ j} {b : FBlock} {k : Nat} (hk : Φ[k]? = some b) (hb : b.Wf Δ)
      (hj : Ctx.SoloP Γ j b.B) :
      FDerives Δ Γ Φ b.Ps (callE b.v j) b.S b.E b.A
  /-- Row weakening. -/
  | sub {Δ Γ Φ Ps e S S' E A} (hle : RowLe S S') (h : FDerives Δ Γ Φ Ps e S E A) :
      FDerives Δ Γ Φ Ps (subE e) S' E A

end BoCa.Fig16.LogRel.Core.Frames

end
