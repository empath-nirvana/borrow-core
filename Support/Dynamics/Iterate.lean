import Paper.S1_Syntax.Definitions
import Support.Syntax.Terms
import Support.Dynamics.Host

/-!
# Support — Dynamics — the loop `iterate`  `[spec §14]`

`Div` is the effect of the reserved name `divEff` with one linear operation, `tick : 1 ↠ Next`,
`Next = 1 ⊕ 1`: `inj₁ ()` is the answer *next* and `inj₂ ()` the answer *close*.

`iterate (f, s)` continues as `iterNext f s`:

    (f s).1 to r. case r { inl b  → inl b
                         | inr s′ → tick () to n. case n { inl _ → iterate (f, s′)
                                                         | inr _ → (λq. inr q) ((f s′).2) } }

`f` is the step: its first observation is one turn, answering `inl` of the result or `inr` of the
next state; its second hands back the residual. The loop ticks at each back edge, so every turn
after the first is guarded by a tick, whoever wrote the step.
-/

namespace BoCa

/-- The name of `Div`, reserved: no program's effect is given it.  `[spec §14]` -/
def divEff : UInt32 := 0xFFFFFFFF

/-- The answer *next*, `inj₁ ()`.  `[spec §14]` -/
def nextV : Val := .inj₁ .unit

/-- The answer *close*, `inj₂ ()`.  `[spec §14]` -/
def closeV : Val := .inj₂ .unit

/-- `tick ()`: `perform (divEff, (0, ()))`.  `[spec §14]` -/
def tickE : Expr :=
  .app (.val (.prim .perform)) (.val (.pair (.i32 divEff) (.pair (.i32 0) .unit)))

/-- `λq. inr q`. -/
def inrV : Val := .lam (.inj₂ (.var 0))

/-- After the tick, under the answer's payload (`0`), the answer `n` (`1`) and the state `s′`
(`2`): `iterate (f, s′)`, or `(λq. inr q) ((f s′).2)`. -/
def iterTurn (f : Val) : Expr :=
  .case (.var 0)
    (.app (.val (.prim .iterate)) (.pair (.val (f.shift 3 0)) (.var 2)))
    (.app (.val inrV) (.app (.app (.val (f.shift 3 0)) (.var 2)) (.val closeV)))

/-- One step of `iterate (f, s)`: the turn `(f s).1`, and on `inr s′` the tick and the case on
its answer.  The branches bind the turn's answer and the tick's, so `f` is shifted past them.
`[spec §14]` -/
def iterNext (f s : Val) : Expr :=
  .case (.app (.app (.val f) (.val s)) (.val nextV))
    (.inj₁ (.var 0))
    (.app (.val (.lam (iterTurn f))) tickE)

end BoCa
