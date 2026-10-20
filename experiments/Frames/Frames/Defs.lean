import Core

/-!
# Frames — the frame type, the exit row and the elaborated terms  `[draft: docs/research/frames-with-exits.md]`

A **frame** is a computation that holds a tuple `Π` of *slots* (places: an owned cell `Ref A`
or a borrow `Mut @a A`) and may leave by several local exits. Its type is a **derived**
computation type, built from Core's formers only:

    Fr Σ Π E A  ≜  Π ⊸ F_Σ (Π ⊗ (A ⊕ ⊕E))          (`frTy`)

- `A` is the normal answer; `E` is the **exit row**, a stack of the local exits the frame may
  leave by (`break` and `continue` of an enclosing loop, a labelled block's exit, the function's
  early `return`), innermost first, each with its payload type;
- every exit hands back `Π` beside its tag: the slots come back on every exit, once, because
  `Π ⊗ −` is a factor of the answer, not a summand;
- `raise` and every other abortive operation are not in `E`: they are in the row `Σ`, and leave
  by §19's unwinding (the frame's Core code holds its slots under `[then]` finalisers, and lends
  them by the unwinding forms `withborU`). That is the agreement with §19 (`Theorems.lean`).

No `VTy`, `CTy` or `CDerives` constructor is added. This file holds the types and the terms the
frame rules elaborate to; `Rules.lean` holds the judgment.

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

/-- The answer of a frame with normal answer `A`: `A ⊕ ⊕E`. -/
def exitsTy (A : VTy) (E : ExitRow) : VTy := .sum A E.sumTy

/-! ### Slots and the frame type -/

/-- The slot tuple `Π = P₀ ⊗ (P₁ ⊗ … ⊗ 1)`. -/
def slotsTy : List VTy → VTy
  | [] => .unit
  | P :: Ps => .tensor P (slotsTy Ps)

/-- **The frame type** `Fr Σ Π E A ≜ Π ⊸ F_Σ (Π ⊗ (A ⊕ ⊕E))`: a derived computation type. -/
def frTy (S : Row) (Ps : List VTy) (E : ExitRow) (A : VTy) : CTy :=
  .arr (slotsTy Ps) (CTy.effOf S (.tensor (slotsTy Ps) (exitsTy A E)))

/-- A frame-typed block: `!U(B ⊸ Fr Σ Π E A)`, the type of a closure that writes the places of
`Π` (§41 R3's `!U(W ⊗ A ⊸ F_r (W ⊗ B))`, with `W` the slots and the exits added). -/
def blockTy (B : VTy) (S : Row) (Ps : List VTy) (E : ExitRow) (A : VTy) : VTy :=
  .bang (.thunk (.arr B (frTy S Ps E A)))

/-- What a slot may hold, with its destructor: an owned cell whose content has one, or a `mut`
borrow (its destructor `forget`). -/
inductive SlotOk : VTy → Prop where
  | ref {A : VTy} (h : HasDtor A) : SlotOk (.ref A)
  | «mut» {a : Lifetime.Life} {A : VTy} : SlotOk (.mut a A)

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
exit: `λπ. N↑ then x. (π, inl x) unwind dtor_Π π`.
In the continuation: `0 = x`, `1 = π`; in the finaliser: `0 = ()`, `1 = π`. -/
def coreE (Ps : List VTy) (N : Expr) : Expr :=
  .lam (thenE (.pair (.var 1) (.inj₁ (.var 0))) (.app (dtorE (slotsTy Ps)) (.var 1)) (sh 1 N))

/-- **`exit k V`**: leave by the `k`-th exit of the row with payload `V`: `λπ. (π, inr (inj_k V↑))`. -/
def exitE (k : Nat) (V : Expr) : Expr :=
  .lam (.pair (.var 0) (.inj₂ (injAt k (sh 1 V))))

/-- **`bind M (x. N)`**: `λπ. M π to (π', r). case r {inl a → N[a] π' | inr e → (π', inr e)}`.
`eN` is `N`'s elaboration, under `a`.
After `let (π', r)`: `0 = r`, `1 = π'`, `2 = x`, `3 = π`, `4… = Γ`; in a branch one more. -/
def bindE (eM eN : Expr) : Expr :=
  seqE eM (.letpair (.var 0)
    (.case (.var 0)
      (.app (.app (sh 5 (.val (.lam eN))) (.var 0)) (.var 2))
      (.pair (.var 2) (.inj₂ (.var 0)))))

/-- **`case V (x. M₁) (y. M₂)`**: `λπ. case V↑ {inl x → M₁[x] π | inr y → M₂[y] π}`.
In a branch: `0 = x`, `1 = π`, `2… = Γ`. -/
def caseE (V e₁ e₂ : Expr) : Expr :=
  .lam (.case (sh 1 V)
    (.app (.app (sh 2 (.val (.lam e₁))) (.var 0)) (.var 1))
    (.app (.app (sh 2 (.val (.lam e₂))) (.var 0)) (.var 1)))

/-- **`catch M (b. H)`**: run `M`, whose row has one more exit at its head; that exit is caught
and `H` runs on its payload. Every other answer passes on, the row's tail re-indexed by the
`case` itself:
`λπ. M π to (π', r). case r {inl a → (π', inl a) | inr e → case e {inl b → H[b] π' | inr e' → (π', inr e')}}`.
In the inner branches: `0 = b`/`e'`, `1 = e`, `2 = r`, `3 = π'`, `4 = x`, `5 = π`, `6… = Γ`. -/
def catchE (eM eH : Expr) : Expr :=
  seqE eM (.letpair (.var 0)
    (.case (.var 0)
      (.pair (.var 2) (.inj₁ (.var 0)))
      (.case (.var 0)
        (.app (.app (sh 6 (.val (.lam eH))) (.var 0)) (.var 3))
        (.pair (.var 3) (.inj₂ (.var 0))))))

/-- **`under M`**: a frame over `Π` run in a frame over `Q :: Π`, the head slot held aside:
`λπ. let (q, ρ) = π; M ρ then y. let (ρ', r) = y; ((q, ρ'), r) unwind dtor_Q q`.
After `let (q, ρ)`: `0 = ρ`, `1 = q`, `2 = π`, `3… = Γ`. -/
def underE (Q : VTy) (eM : Expr) : Expr :=
  .lam (.letpair (.var 0)
    (thenE (.letpair (.var 0) (.pair (.pair (.var 4) (.var 1)) (.var 0)))
      (.app (dtorE Q) (.var 2))
      (.app (sh 3 eM) (.var 0))))

/-- **`use N`**: the head slot lent, by the unwinding borrow constant, to a Core callback `N`;
the rest held aside:
`λπ. let (p, ρ) = π; (λf. (λw. (w p f) then y. let (p', b) = y; ((p', ρ), inl b) unwind dtor_Π ρ) withborU) N↑`.
After the binds: `0 = w`, `1 = f`, `2 = ρ`, `3 = p`, `4 = π`, `5… = Γ`. -/
def useE (src : LendSrc) (Ps : List VTy) (N : Expr) : Expr :=
  .lam (.letpair (.var 0)
    (.app (.val (.lam
      (.app (.val (.lam
        (thenE (.letpair (.var 0) (.pair (.pair (.var 1) (.var 5)) (.inj₁ (.var 0))))
          (.app (dtorE (slotsTy Ps)) (.var 3))
          (.app (.app (.var 0) (.var 3)) (.var 1)))))
        (withborUE src.fin))))
      (sh 3 N)))

/-- **`lend M`**: the head slot reborrowed at a fresh `'x` for a frame `M` over
`Mut 'x A :: Π_rest`; the inner frame's head is forgotten at its end, the rest comes back boxed:
`λπ. let (p, ρ) = π; withborU p (Λ. λb. M (b, ρ) to y. let (ρ'', r) = y; let (b', ρ') = ρ''; forget b'; (ρ', r))
      to y. let (p', z) = y; let (ρ', r) = z; ((p', ρ'), r)`.
In the callback: `0 = b`, `1 = ()`, `2 = ρ`, `3 = p`, `4 = π`, `5… = Γ`. -/
def lendE (src : LendSrc) (eM : Expr) : Expr :=
  let cb : Expr :=
    .val (.lam (.val (.lam
      (.app (.val (.lam
        (.app (.val (.lam
          (.letpair (.var 0) (.letpair (.var 1)
            (.seq (.app forget (.var 1)) (.pair (.var 0) (.var 2)))))))
          (.app (sh 6 eM) (.var 0)))))
        (.pair (.var 0) (.var 2))))))
  .lam (.letpair (.var 0)
    (.app (.val (.lam
      (.app (.val (.lam
        (.app (.val (.lam
          (.letpair (.var 0) (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0))))))
          (.app (.app (.var 0) (.var 3)) (.var 1)))))
        (withborUE src.fin))))
      cb))

/-- **`new V M`**: a new slot, a cell holding `V`, for the frame `M` over `Ref A :: Π`. At the
normal exit the cell is freed and its content handed out beside `M`'s answer; at every other
exit it is destroyed:
`λπ. (λc. (λcp. M cp to y. let (π'', r) = y; let (c', π') = π'';
        case r {inl b → (λa. (π', inl (b, a))) (free c') | inr e → dtor_{Ref A} c'; (π', inr e)}) (c, π)) (alloc V↑)`. -/
def newE (A : VTy) (V eM : Expr) : Expr :=
  .lam (.app (.val (.lam
    (.app (.val (.lam
      (.app (.val (.lam
        (.letpair (.var 0) (.letpair (.var 1)
          (.case (.var 2)
            (.app (.val (.lam (.pair (.var 2) (.inj₁ (.pair (.var 1) (.var 0))))))
              (.app (.val (.prim .free)) (.var 2)))
            (.seq (.app (dtorE (.ref A)) (.var 2)) (.pair (.var 1) (.inj₂ (.var 0)))))))))
        (.app (sh 3 eM) (.var 0)))))
      (.pair (.var 0) (.var 1)))))
    (.app (.val (.prim .alloc)) (sh 1 V)))

/-- The step of a counted loop: `λ(i, (π, s)). M[i, s] π to (π', r). case r {inl s' → inl (π', s') | inr x → inr (π', x)}`.
`eM` is the turn's elaboration under the counter `i` (index 1) and the state `s` (index 0).
After the two `let`s: `0 = s`, `1 = π`, `2 = st`, `3 = i`, `4 = arg`, `5… = Γ`. -/
def countStepE (eM : Expr) : Expr :=
  .val (.lam (.letpair (.var 0) (.letpair (.var 0)
    (.app (.val (.lam
      (.letpair (.var 0) (.case (.var 0)
        (.inj₁ (.pair (.var 2) (.var 0)))
        (.inj₂ (.pair (.var 2) (.var 0)))))))
      (.app (.app (.app (sh 5 (.val (.lam (.val (.lam eM))))) (.var 3)) (.var 0)) (.var 1))))))

/-- **`loopCount n s₀ M`**: the counted loop with an exit (`count_try`, §16) whose state is the
slots and the loop's own state, its turn the frame `M`; the head exit of `M`'s row is the loop's
`break`, the turn's normal answer the next state (`continue` is a `catch` around the turn):
`λπ. (λr. case r {inl (π', s) → (π', inl (inl s)) | inr (π', inl b) → (π', inl (inr b)) | inr (π', inr e) → (π', inr e)})
      (count_try (step, (n, (0, (π, s₀)))))`. -/
def loopCountE (n s₀ eM : Expr) : Expr :=
  .lam (.app (.val (.lam
    (.case (.var 0)
      (.letpair (.var 0) (.pair (.var 1) (.inj₁ (.inj₁ (.var 0)))))
      (.letpair (.var 0) (.case (.var 0)
        (.pair (.var 2) (.inj₁ (.inj₂ (.var 0))))
        (.pair (.var 2) (.inj₂ (.var 0))))))))
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
        (.letpair (.var 0) (.case (.var 0)
          (.inj₂ (.pair (.var 2) (.var 0)))
          (.inj₁ (.pair (.var 2) (.var 0)))))))
        (.app (.app (sh 5 (.val (.lam eM))) (.var 2)) (.var 3)))
      (.seq (.app (dtorE S₀) (.var 2)) (.pair (.var 3) (.val .unit))))))

/-- **`loopIter s₀ M`**: the div loop (`iterate`, §14) over the slots and the loop's state:
`λπ. (λstep. (λw. (λa. (λr. case r {inl (π', inl b) → (π', inl (inl b)) | inl (π', inr e) → (π', inr e)
                                      | inr (π', ()) → (π', inl (inr ()))}) (w a)) (step, (π, s₀))) iterate) step`.
After the binds: `0 = a`, `1 = w`, `2 = step`, `3 = π`, `4… = Γ`. -/
def loopIterE (S₀ : VTy) (s₀ eM : Expr) : Expr :=
  .lam (.app (.val (.lam
    (.app (.val (.lam
      (.app (.val (.lam
        (.app (.val (.lam
          (.case (.var 0)
            (.letpair (.var 0) (.case (.var 0)
              (.pair (.var 2) (.inj₁ (.inj₁ (.var 0))))
              (.pair (.var 2) (.inj₂ (.var 0)))))
            (.letpair (.var 0) (.pair (.var 1) (.inj₁ (.inj₂ (.val .unit))))))))
          (.app (.var 1) (.var 0)))))
        (.pair (.var 1) (.pair (.var 2) (sh 3 s₀))))))
      (.val (.prim .iterate)))))
    (sh 1 (iterStepE S₀ eM)))

/-- **`callBlock b V`**: call a frame-typed block (a closed value) on `V` with the current slots:
`λπ. (b V↑) π`. ANF: `V` is a variable of the frame's context. -/
def callE (b : Val) (j : Nat) : Expr :=
  .lam (.app (.app (.val b) (.var (j + 1))) (.var 0))

/-- **Row weakening**: `λπ. e↑ π`. -/
def subE (e : Expr) : Expr := .lam (.app (sh 1 e) (.var 0))

/-! ### Cheap facts about the types -/

/-- The frame type is Core's: an arrow into an effectful returner. -/
theorem frTy_eq (S : Row) (Ps : List VTy) (E : ExitRow) (A : VTy) :
    frTy S Ps E A = .arr (slotsTy Ps) (CTy.effOf S (.tensor (slotsTy Ps) (.sum A E.sumTy))) := rfl

/-- At the empty row and no exits, a frame over no slots is `1 ⊸ F(1 ⊗ (A ⊕ 0))`. -/
theorem frTy_nil (A : VTy) :
    frTy [] [] [] A = .arr .unit (.ret (.tensor .unit (.sum A .zero))) := rfl

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

/-- Every slot type is one of the two kinds, and each has a destructor. -/
theorem SlotOk.hasDtor {P : VTy} (h : SlotOk P) : HasDtor P := by
  cases h with
  | ref h => exact .ref h
  | «mut» => exact .mut

theorem SlotsOk.hasDtor : ∀ {Ps : List VTy}, SlotsOk Ps → HasDtor (slotsTy Ps)
  | [], _ => .unit
  | P :: Ps, h => .tensor (h P (by simp)).hasDtor (SlotsOk.hasDtor fun Q hQ => h Q (by simp [hQ]))

end BoCa.Fig16.LogRel.Core.Frames

end
