import Core.EffPrograms
import Core.InsertDead
import Core.EffCancelRuns
import Core.Dtor
import Core.Steps

/-!
# Core — frames with typed exits and typestate slots: the types and the terms  `[spec §47]`

A **frame** is a computation that holds a tuple of *slots* (places: an owned cell `Ref A` or a
borrow `Mut @a A`, or a cell whose content is not known statically, `Ref A ⊕ Ref B`) and may
leave by several local exits. Its type is a **derived** computation type, built from Core's
formers only:

    Fr Σ Π Πn Πx E A  ≜  Π ⊸ F_Σ ((Πn ⊗ A) ⊕ (Πx ⊗ ⊕E))          (`frTy`)

- `Π` is the slots' state on entry, `Πn` at the normal exit, `Πx` at every local exit: a slot's
  type may change in the frame (a move out of a cell is `swap c ()`, a put back `swap c a`), and
  the exits share one state;
- `A` is the normal answer; `E` is the **exit row**, a stack of the local exits the frame may
  leave by (`break` and `continue` of an enclosing loop, a labelled block's exit, the function's
  early `return`), innermost first, each with its payload type;
- every exit hands back the slots beside its tag: `Πn ⊗ −` and `Πx ⊗ −` are factors of the two
  summands of the answer, so the slots come back on every exit, once;
- `raise` and every other abortive operation are not in `E`: they are in the row `Σ`, and leave
  by §19's unwinding (the frame's Core code holds its slots under `[then]` finalisers, and lends
  them by the unwinding forms `withborU`).

At `Π = Πn = Πx` this is #632's `Π ⊸ F_Σ (Π ⊗ (A ⊕ ⊕E))` with the slots distributed over the
sum. No `VTy`, `CTy` or `CDerives` constructor is added. This file holds the types and the terms
the frame rules elaborate to; `Core/FramesRules.lean` holds the judgment.

**De Bruijn conventions.** A frame's elaboration is a λ-value `λπ. body`; inside `body` the slot
tuple `π` is variable `0` and the frame's context `Γ` starts at `1`. Each term below says what
each index is where it is used.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Frames
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The exit row -/

/-- An exit row: the local exits a frame may leave by, innermost first, each a label (static,
as a handler's name is, §19) and its payload type. It is a stack: the innermost catcher
(`catch`, a loop) removes its head, so exits are de Bruijn indices into the enclosing catchers,
and lexical nesting is the only order they are caught in. -/
abbrev ExitRow := List (Nat × VTy)

/-- `⊕E = E₀ ⊕ (E₁ ⊕ (… ⊕ 0))`. -/
def ExitRow.sumTy : ExitRow → VTy
  | [] => .zero
  | (_, B) :: E => .sum B (ExitRow.sumTy E)

/-- The normal answer and the exits: `A ⊕ ⊕E`, the payload of a loop's turn's exit sum. -/
def exitsTy (A : VTy) (E : ExitRow) : VTy := .sum A E.sumTy

/-! ### Slots and the frame type -/

/-- The slot tuple `Π = P₀ ⊗ (P₁ ⊗ … ⊗ 1)`. -/
def slotsTy : List VTy → VTy
  | [] => .unit
  | P :: Ps => .tensor P (slotsTy Ps)

/-- The answer of a frame: `(Πn ⊗ A) ⊕ (Πx ⊗ ⊕E)`. -/
def ansTy (Pn X : List VTy) (A : VTy) (E : ExitRow) : VTy :=
  .sum (.tensor (slotsTy Pn) A) (.tensor (slotsTy X) E.sumTy)

/-- **The frame type** `Fr Σ Π Πn Πx E A ≜ Π ⊸ F_Σ ((Πn ⊗ A) ⊕ (Πx ⊗ ⊕E))`: a derived
computation type. -/
def frTy (S : Row) (P Pn X : List VTy) (E : ExitRow) (A : VTy) : CTy :=
  .arr (slotsTy P) (CTy.effOf S (ansTy Pn X A E))

/-- A frame-typed block: `!U(B ⊸ Fr Σ Π Πn Πx E A)`, the type of a closure that writes the places
of `Π` (§41 R3's `!U(W ⊗ A ⊸ F_r (W ⊗ B))`, with `W` the slots and the exits added). -/
def blockTy (B : VTy) (S : Row) (P Pn X : List VTy) (E : ExitRow) (A : VTy) : VTy :=
  .bang (.thunk (.arr B (frTy S P Pn X E A)))

/-- What a slot may hold, with its destructor: an owned cell whose content has one, a `mut`
borrow (its destructor `forget`), or a cell in one of two states, the tag its drop flag. -/
inductive SlotOk : VTy → Prop where
  | ref {A : VTy} (h : HasDtor A) : SlotOk (.ref A)
  | «mut» {a : Lifetime.Life} {A : VTy} : SlotOk (.mut a A)
  | sum {P Q : VTy} (h₁ : SlotOk P) (h₂ : SlotOk Q) : SlotOk (.sum P Q)

/-- Every live slot of a Core context has a destructor: what an exit's drop glue needs of the
continuation it skips. -/
def CtxDtor (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → HasDtor s.ty

/-- Every slot of `Π` has a destructor. -/
def SlotsOk (Ps : List VTy) : Prop := ∀ P ∈ Ps, SlotOk P

/-- The rows a frame's held Core code runs at: `[then]` at option A (`CDerives.effThenA`) with its
side conditions discharged once. -/
def FRow (S : Row) : Prop := S.NZ ∧ S.Uniq ∧ ¬ S.UnrD

/-- How a slot is lent to a callback: the source type of the unwinding borrow constant.
`ref` is `withbor` (2) at `Ref A`, `mut` is `withbor` (3) at `Mut @a A`. -/
inductive LendSrc where
  | ref (A : VTy)
  | «mut» (a : Lifetime.Life) (A : VTy)

/-- The source's type. -/
def LendSrc.ty : LendSrc → VTy
  | .ref A => .ref A
  | .mut a A => .mut a A

/-- The lent payload's type. -/
def LendSrc.payload : LendSrc → VTy
  | .ref A => A
  | .mut _ A => A

/-- The source's finaliser on an unwind: the destructor of the owned cell, `forget` of a borrow
(§19: "the elaborator passes the source's destructor `dtorE src`"). -/
def LendSrc.fin (s : LendSrc) : Expr := dtorE s.ty

/-! ### Typestate: a cell's states, and widening -/

/-- The state of a frame's own cell (`new`'s slot) at its normal exit: full of a content of type
`A` (a hole is `full 1`), or one of two states, the tag its drop flag. -/
inductive CellSt where
  | full (A : VTy)
  | sum (s t : CellSt)

/-- The slot type of a cell state: `Ref A`, or `P ⊕ Q`. -/
def CellSt.ty : CellSt → VTy
  | .full A => .ref A
  | .sum s t => .sum s.ty t.ty

/-- What the cell holds: `A`, or `C ⊕ D`. -/
def CellSt.content : CellSt → VTy
  | .full A => A
  | .sum s t => .sum s.content t.content

/-- Every state's content has a destructor. -/
def CellSt.Ok : CellSt → Prop
  | .full A => HasDtor A
  | .sum s t => s.Ok ∧ t.Ok

/-- The release of a cell at its state: `free`, under the case on the tags:
`rel (full A) = λc. free c`, `rel (s ⊕ t) = λc. case c {inl d → inl (rel s d) | inr d → inr (rel t d)}`. A
closed λ-value. -/
def CellSt.relE : CellSt → Expr
  | .full _ => .val (.lam (.app (.val (.prim .free)) (.var 0)))
  | .sum s t => .val (.lam (.case (.var 0) (.inj₁ (.app s.relE (.var 0))) (.inj₂ (.app t.relE (.var 0)))))

/-- One slot's widening into a state with a tag: kept, or injected into a sum. -/
inductive WStep where
  | keep
  | inl
  | inr

/-- The widened slot's term, `e` itself or its injection. -/
def WStep.apply : WStep → Expr → Expr
  | .keep, e => e
  | .inl, e => .inj₁ e
  | .inr, e => .inj₂ e

/-- A slot type widened by a step to another. -/
inductive WStep.Ok : WStep → VTy → VTy → Prop where
  | keep {P : VTy} : WStep.Ok .keep P P
  | inl {P Q : VTy} : WStep.Ok .inl P (.sum P Q)
  | inr {P Q : VTy} : WStep.Ok .inr Q (.sum P Q)

/-- A slot tuple widened slot by slot. -/
inductive Widens : List WStep → List VTy → List VTy → Prop where
  | nil : Widens [] [] []
  | cons {w : WStep} {ws : List WStep} {P Q : VTy} {Ps Qs : List VTy} (h : w.Ok P Q)
      (hs : Widens ws Ps Qs) : Widens (w :: ws) (P :: Ps) (Q :: Qs)

/-- The widening of a slot tuple, a closed λ-value: `wid [] = λπ. π`,
`wid (w :: ws) = λπ. let (p, ρ) = π; (w p, wid ws ρ)`. -/
def widE : List WStep → Expr
  | [] => .val (.lam (.var 0))
  | w :: ws => .val (.lam (.letpair (.var 0) (.pair (w.apply (.var 1)) (.app (widE ws) (.var 0)))))

/-! ### Terms -/

/-- `e` shifted past `k` binders. -/
abbrev sh (k : Nat) (e : Expr) : Expr := e.shift k 0

/-- The injection into `⊕E` at position `k`. -/
def injAt : Nat → Expr → Expr
  | 0, v => .inj₁ v
  | k + 1, v => .inj₂ (injAt k v)

/-- `M to x. K` with `π` handed through: `λπ. (λx. K) (M↑ π)`.
In `K`: `0 = x`, `1 = π` (consumed by `M`), `2… = Γ`. -/
def seqE (eM K : Expr) : Expr :=
  .lam (.app (.val (.lam K)) (.app (sh 1 eM) (.var 0)))

/-- **`core N`**: a Core computation run while the frame holds its slots, its answer the normal
exit: `λπ. N↑ then x. inl (π, x) unwind dtor_Π π`.
In the continuation: `0 = x`, `1 = π`; in the finaliser: `0 = ()`, `1 = π`. -/
def coreE (Ps : List VTy) (N : Expr) : Expr :=
  .lam (thenE (.inj₁ (.pair (.var 1) (.var 0))) (.app (dtorE (slotsTy Ps)) (.var 1)) (sh 1 N))

/-- **`exit k V`**: leave by the `k`-th exit of the row with payload `V`:
`λπ. inr (π, inj_k V↑)`. -/
def exitE (k : Nat) (V : Expr) : Expr :=
  .lam (.inj₂ (.pair (.var 0) (injAt k (sh 1 V))))

/-- **Drop glue for a skipped continuation.** `dropCtxE Γ i k`: the destructor of each live slot
of `Γ`, the slot at index `i` onwards, then `k`. An exit that skips a continuation runs it on the
continuation's context: the context's linear values are Core values, not slots, so §19's drop
glue (`dropE`) disposes of them. -/
def dropCtxE : Ctx VTy → Nat → Expr → Expr
  | [], _, k => k
  | ⟨T, true⟩ :: Γ, i, k => dropE T i (dropCtxE Γ (i + 1) k)
  | ⟨_, false⟩ :: Γ, i, k => dropCtxE Γ (i + 1) k

/-- The arm of an exit that skips a continuation, at the exit `z = (π', e)` (variable `0`):
when the row is empty, the payload is `0` and the arm is `let (π', e) = z; inr (π', absurd e)`,
with no drop glue (`absurd` drops its context); else the drop glue `d`. The slots are handed
back on both, so the arm returns them whatever the payload is at run time. -/
def exitArmE : ExitRow → Expr → Expr
  | [], _ => .letpair (.var 0) (.inj₂ (.pair (.var 1) (absurdE (.var 0))))
  | _ :: _, d => d

/-- **`bind M (x. N)`**: `λπ. M π to r. case r {inl z → let (π', a) = z; N[a] π' | inr z → drop Γ₂; inr z}`.
`eN` is `N`'s elaboration, under `a`; `Γ₂` is `N`'s context, which the exit arm drops.
In the normal arm, after the `let`: `0 = a`, `1 = π'`, `2 = z`, `3 = r`, `4 = π`, `5… = Γ`; in
the exit arm: `0 = z`, `1 = r`, `2 = π`, `3… = Γ`. -/
def bindE (E : ExitRow) (Γ₂ : Ctx VTy) (eM eN : Expr) : Expr :=
  seqE eM (.case (.var 0)
    (.letpair (.var 0) (.app (.app (sh 5 (.val (.lam eN))) (.var 0)) (.var 1)))
    (exitArmE E (dropCtxE Γ₂ 3 (.inj₂ (.var 0)))))

/-- **`case V (x. M₁) (y. M₂)`**: `λπ. case V↑ {inl x → M₁[x] π | inr y → M₂[y] π}`.
In a branch: `0 = x`, `1 = π`, `2… = Γ`. -/
def caseE (V e₁ e₂ : Expr) : Expr :=
  .lam (.case (sh 1 V)
    (.app (.app (sh 2 (.val (.lam e₁))) (.var 0)) (.var 1))
    (.app (.app (sh 2 (.val (.lam e₂))) (.var 0)) (.var 1)))

/-- **`catch M (b. H)`**: run `M`, whose row has one more exit at its head; that exit is caught
and `H` runs on its payload and the exit's slots. Every other answer passes on, the row's tail
re-indexed by the `case` itself, after the drop glue of `H`'s context `Γ₂`:
`λπ. M π to r. case r {inl z → drop Γ₂; inl z | inr z → let (π', e) = z; case e {inl b → H[b] π' | inr e' → drop Γ₂; inr (π', e')}}`.
In the normal arm: `0 = z`, `1 = r`, `2 = π`, `3… = Γ`; in the inner branches: `0 = b`/`e'`,
`1 = e`, `2 = π'`, `3 = z`, `4 = r`, `5 = π`, `6… = Γ`. -/
def catchE (Γ₂ : Ctx VTy) (eM eH : Expr) : Expr :=
  seqE eM (.case (.var 0)
    (dropCtxE Γ₂ 3 (.inj₁ (.var 0)))
    (.letpair (.var 0) (.case (.var 0)
      (.app (.app (sh 6 (.val (.lam eH))) (.var 0)) (.var 2))
      (dropCtxE Γ₂ 6 (.inj₂ (.pair (.var 2) (.var 0)))))))

/-- The answer `y` (variable `0`) with the slot at variable `h` put back at the head of its
slots, on both arms: `case y {inl z → let (ρ, a) = z; inl ((q, ρ), a) | inr z → let (ρ, e) = z; inr ((q, ρ), e)}`. -/
def consAnsE (h : Nat) : Expr :=
  .case (.var 0)
    (.letpair (.var 0) (.inj₁ (.pair (.pair (.var (h + 3)) (.var 1)) (.var 0))))
    (.letpair (.var 0) (.inj₂ (.pair (.pair (.var (h + 3)) (.var 1)) (.var 0))))

/-- **`under M`**: a frame over `Π` run in a frame over `Q :: Π`, the head slot held aside:
`λπ. let (q, ρ) = π; M ρ then y. (q put back on both arms of y) unwind dtor_Q q`.
After `let (q, ρ)`: `0 = ρ`, `1 = q`, `2 = π`, `3… = Γ`; in the continuation `0 = y`, `2 = q`. -/
def underE (Q : VTy) (eM : Expr) : Expr :=
  .lam (.letpair (.var 0)
    (thenE (consAnsE 2) (.app (dtorE Q) (.var 2)) (.app (sh 3 eM) (.var 0))))

/-- **`use N`**: the head slot lent, by the unwinding borrow constant, to a Core callback `N`;
the rest held aside:
`λπ. let (p, ρ) = π; (λf. (λw. (w p f) then y. let (p', b) = y; inl ((p', ρ), b) unwind dtor_Π ρ) withborU) N↑`.
After the binds: `0 = w`, `1 = f`, `2 = ρ`, `3 = p`, `4 = π`, `5… = Γ`. -/
def useE (src : LendSrc) (Ps : List VTy) (N : Expr) : Expr :=
  .lam (.letpair (.var 0)
    (.app (.val (.lam
      (.app (.val (.lam
        (thenE (.letpair (.var 0) (.inj₁ (.pair (.pair (.var 1) (.var 5)) (.var 0))))
          (.app (dtorE (slotsTy Ps)) (.var 3))
          (.app (.app (.var 0) (.var 3)) (.var 1)))))
        (withborUE src.fin))))
      (sh 3 N)))

/-- The inner frame's answer `y` (variable `0`) under a lend, its head borrow forgotten on both
arms: `case y {inl z → let (ρ'', a) = z; let (b, ρ) = ρ''; forget b; inl (ρ, a) | inr z → … inr (ρ, e)}`. -/
def forgetHeadE : Expr :=
  .case (.var 0)
    (.letpair (.var 0) (.letpair (.var 1)
      (.seq (.app forget (.var 1)) (.inj₁ (.pair (.var 0) (.var 2))))))
    (.letpair (.var 0) (.letpair (.var 1)
      (.seq (.app forget (.var 1)) (.inj₂ (.pair (.var 0) (.var 2))))))

/-- **`lend M`**: the head slot reborrowed at a fresh `'x` for a frame `M` over
`Mut 'x A :: Π_rest`; the inner frame's head is forgotten at each of its exits, the rest comes
back boxed, and the source is put back on both arms:
`λπ. let (p, ρ) = π; withborU p (Λ. λb. M (b, ρ) to y. forgetHead y) to y. let (p', z) = y; z with p' put back`.
In the callback: `0 = b`, `1 = ()`, `2 = ρ`, `3 = p`, `4 = π`, `5… = Γ`. -/
def lendE (src : LendSrc) (eM : Expr) : Expr :=
  let cb : Expr :=
    .val (.lam (.val (.lam
      (.app (.val (.lam
        (.app (.val (.lam forgetHeadE))
          (.app (sh 6 eM) (.var 0)))))
        (.pair (.var 0) (.var 2))))))
  .lam (.letpair (.var 0)
    (.app (.val (.lam
      (.app (.val (.lam
        (.app (.val (.lam (.letpair (.var 0) (consAnsE 1))))
          (.app (.app (.var 0) (.var 3)) (.var 1)))))
        (withborUE src.fin))))
      cb))

/-- The inner frame's answer `y` (variable `0`) at the end of a cell's scope: at the normal exit
the cell is released (`rel`) and its content handed out beside the answer; at the exits it is
destroyed (`dtor_Q'`):
`case y {inl z → let (cπ, b) = z; let (c, π) = cπ; (λa. inl (π, (b, a))) (rel c) | inr z → let (cπ, e) = z; let (c, π) = cπ; dtor c; inr (π, e)}`. -/
def endCellE (q : CellSt) (Q' : VTy) : Expr :=
  .case (.var 0)
    (.letpair (.var 0) (.letpair (.var 1)
      (.app (.val (.lam (.inj₁ (.pair (.var 1) (.pair (.var 3) (.var 0))))))
        (.app q.relE (.var 1)))))
    (.letpair (.var 0) (.letpair (.var 1)
      (.seq (.app (dtorE Q') (.var 1)) (.inj₂ (.pair (.var 0) (.var 2))))))

/-- **`new V M`**: a new slot, a cell holding `V`, for the frame `M` over `Ref A :: Π`. At the
normal exit the cell, in state `q`, is released and its content handed out beside `M`'s answer;
at every other exit, in state `Q'`, it is destroyed:
`λπ. (λc. (λcp. M cp to y. endCell y) (c, π)) (alloc V↑)`. -/
def newE (q : CellSt) (Q' : VTy) (V eM : Expr) : Expr :=
  .lam (.app (.val (.lam
    (.app (.val (.lam
      (.app (.val (.lam (endCellE q Q')))
        (.app (sh 3 eM) (.var 0)))))
      (.pair (.var 0) (.var 1)))))
    (.app (.val (.prim .alloc)) (sh 1 V)))

/-- **`swap V`**: the head slot `Ref A` swapped for `V : B`, the slot now `Ref B` and the old
content the answer (`swap c ()` is a move out, `swap c a` a put back):
`λπ. let (c, ρ) = π; (λy. let (c', a) = y; inl ((c', ρ), a)) (swap c V↑)`.
After `let (c, ρ)`: `0 = ρ`, `1 = c`, `2 = π`, `3… = Γ`. -/
def swapSE (V : Expr) : Expr :=
  .lam (.letpair (.var 0)
    (.app (.val (.lam (.letpair (.var 0) (.inj₁ (.pair (.pair (.var 1) (.var 3)) (.var 0))))))
      (.app (.app swap (.var 1)) (sh 3 V))))

/-- **`caseSlot M₁ M₂`**: the case on the head slot's tag, `M₁` on its first state and `M₂` on
its second, the same cell in both:
`λπ. let (p, ρ) = π; case p {inl p₁ → (λπ'. M₁ π') (p₁, ρ) | inr p₂ → (λπ'. M₂ π') (p₂, ρ)}`.
In a branch: `0 = pᵢ`, `1 = ρ`, `2 = p`, `3 = π`, `4… = Γ`; under `λπ'` one more. -/
def caseSlotE (e₁ e₂ : Expr) : Expr :=
  .lam (.letpair (.var 0)
    (.case (.var 1)
      (.app (.val (.lam (.app (sh 5 e₁) (.var 0)))) (.pair (.var 0) (.var 1)))
      (.app (.val (.lam (.app (sh 5 e₂) (.var 0)))) (.pair (.var 0) (.var 1)))))

/-- **`widen M`**: the slots at each exit widened into states with tags:
`λπ. M π to y. case y {inl z → let (π', a) = z; inl (wid ws π', a) | inr z → let (π', e) = z; inr (wid wx π', e)}`. -/
def widenE (ws wx : List WStep) (eM : Expr) : Expr :=
  seqE eM (.case (.var 0)
    (.letpair (.var 0) (.inj₁ (.pair (.app (widE ws) (.var 1)) (.var 0))))
    (.letpair (.var 0) (.inj₂ (.pair (.app (widE wx) (.var 1)) (.var 0)))))

/-- The step of a counted loop: `λ(i, (π, s)). M[i, s] π`, the turn's answer itself the step's:
`inl (π', s')` to go on, `inr (π', e)` to leave. `eM` is the turn's elaboration under the counter
`i` (index 1) and the state `s` (index 0). After the two `let`s: `0 = s`, `1 = π`, `2 = st`,
`3 = i`, `4 = arg`, `5… = Γ`. -/
def countStepE (eM : Expr) : Expr :=
  .val (.lam (.letpair (.var 0) (.letpair (.var 0)
    (.app (.app (.app (sh 5 (.val (.lam (.val (.lam eM))))) (.var 3)) (.var 0)) (.var 1)))))

/-- **`loopCount n s₀ M`**: the counted loop with an exit (`count_try`, §16) whose state is the
slots and the loop's own state, its turn the frame `M`; the head exit of `M`'s row is the loop's
`break`, the turn's normal answer the next state (`continue` is a `catch` around the turn). At
the source's end the slots are widened into the exits' state:
`λπ. (λr. case r {inl (π', s) → inl (wid π', inl s) | inr (π', inl b) → inl (π', inr b) | inr (π', inr e) → inr (π', e)})
      (count_try (step, (n, (0, (π, s₀)))))`. -/
def loopCountE (ws : List WStep) (n s₀ eM : Expr) : Expr :=
  .lam (.app (.val (.lam
    (.case (.var 0)
      (.letpair (.var 0) (.inj₁ (.pair (.app (widE ws) (.var 1)) (.inj₁ (.var 0)))))
      (.letpair (.var 0) (.case (.var 0)
        (.inj₁ (.pair (.var 2) (.inj₂ (.var 0))))
        (.inj₂ (.pair (.var 2) (.var 0))))))))
    (.app (.val (.prim .countTry))
      (.pair (sh 1 (countStepE eM))
        (.pair (sh 1 n) (.pair (Val.i32 0).1 (.pair (.var 0) (sh 1 s₀)))))))

/-- The step of a div loop, `λst. let (π, s) = st; ⟨turn, close⟩`: the turn runs `M[s] π` and
answers `inr (π', s')` to go on or `inl (π', x)` to leave; `close` (the loop closed by `Div`'s
handler) destroys the loop's own state and hands back the slots.
Inside `withPair`'s branches: `0 = u`, `1 = sel`, `2 = s`, `3 = π`, `4 = st`, `5… = Γ`. -/
def iterStepE (S₀ : VTy) (eM : Expr) : Expr :=
  .val (.lam (.letpair (.var 0)
    (withPair
      (.app (.val (.lam
        (.case (.var 0) (.inj₂ (.var 0)) (.inj₁ (.var 0)))))
        (.app (.app (sh 5 (.val (.lam eM))) (.var 2)) (.var 3)))
      (.seq (.app (dtorE S₀) (.var 2)) (.pair (.var 3) (.val .unit))))))

/-- **`loopIter s₀ M`**: the div loop (`iterate`, §14) over the slots and the loop's state; the
residual of a closed loop is its slots, widened into the exits' state:
`λπ. (λstep. (λw. (λa. (λr. case r {inl (π', inl b) → inl (π', inl b) | inl (π', inr e) → inr (π', e)
                                      | inr (π', ()) → inl (wid π', inr ())}) (w a)) (step, (π, s₀))) iterate) step`.
After the binds: `0 = a`, `1 = w`, `2 = step`, `3 = π`, `4… = Γ`. -/
def loopIterE (ws : List WStep) (S₀ : VTy) (s₀ eM : Expr) : Expr :=
  .lam (.app (.val (.lam
    (.app (.val (.lam
      (.app (.val (.lam
        (.app (.val (.lam
          (.case (.var 0)
            (.letpair (.var 0) (.case (.var 0)
              (.inj₁ (.pair (.var 2) (.inj₁ (.var 0))))
              (.inj₂ (.pair (.var 2) (.var 0)))))
            (.letpair (.var 0) (.inj₁ (.pair (.app (widE ws) (.var 1)) (.inj₂ (.val .unit))))))))
          (.app (.var 1) (.var 0)))))
        (.pair (.var 1) (.pair (.var 2) (sh 3 s₀))))))
      (.val (.prim .iterate)))))
    (sh 1 (iterStepE S₀ eM)))

/-- **`callBlock b V`**: call a frame-typed block (a closed value) on `V` with the current slots:
`λπ. (λf. f V↑↑ π) b`. ANF: `V` is a variable of the frame's context. -/
def callE (b : Val) (j : Nat) : Expr :=
  .lam (.app (.val (.lam (.app (.app (.var 0) (.var (j + 2))) (.var 1)))) (.val b))

/-- **Row weakening**: `λπ. e↑ π`. -/
def subE (e : Expr) : Expr := .lam (.app (sh 1 e) (.var 0))

/-! ### Cheap facts about the types -/

/-- The frame type is Core's: an arrow into an effectful returner. -/
theorem frTy_eq (S : Row) (P Pn X : List VTy) (E : ExitRow) (A : VTy) :
    frTy S P Pn X E A = .arr (slotsTy P) (CTy.effOf S
      (.sum (.tensor (slotsTy Pn) A) (.tensor (slotsTy X) E.sumTy))) := rfl

/-- At the empty row and no exits, a frame over no slots is `1 ⊸ F((1 ⊗ A) ⊕ (1 ⊗ 0))`. -/
theorem frTy_nil (A : VTy) :
    frTy [] [] [] [] [] A = .arr .unit (.ret (.sum (.tensor .unit A) (.tensor .unit .zero))) := rfl

/-- The `k`-th injection lands at the `k`-th exit's payload: the exit row's position `k` is the
summand `inj_k` selects. -/
theorem sumTy_get {E : ExitRow} {k : Nat} {l : Nat} {B : VTy} (h : E[k]? = some (l, B)) :
    ∃ pre post, E = pre ++ (l, B) :: post ∧ pre.length = k := by
  induction E generalizing k with
  | nil => simp at h
  | cons hd tl ih =>
      cases k with
      | zero => simp at h; exact ⟨[], tl, by simp [h], rfl⟩
      | succ k =>
          simp at h
          obtain ⟨pre, post, rfl, hl⟩ := ih h
          exact ⟨hd :: pre, post, rfl, by simp [hl]⟩

/-- Every slot type has a destructor. -/
theorem SlotOk.hasDtor {P : VTy} (h : SlotOk P) : HasDtor P := by
  induction h with
  | ref h => exact .ref h
  | «mut» => exact .mut
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂

theorem SlotsOk.hasDtor : ∀ {Ps : List VTy}, SlotsOk Ps → HasDtor (slotsTy Ps)
  | [], _ => .unit
  | P :: Ps, h => .tensor (h P (by simp)).hasDtor (SlotsOk.hasDtor fun Q hQ => h Q (by simp [hQ]))

/-- A cell's state is a slot. -/
theorem CellSt.slotOk : ∀ {q : CellSt}, q.Ok → SlotOk q.ty
  | .full _, h => .ref h
  | .sum _ _, h => .sum (CellSt.slotOk h.1) (CellSt.slotOk h.2)

end BoCa.Fig16.LogRel.Core.Frames

end
