import Targets.Statements.Soundness

/-!
# Targets — P8, continuation linearity (DESIGN §6 P8)

**World:** [prog].

A continuation is used as its qualifier says: a linear one is resumed exactly once, an affine one
resumed or cancelled exactly once.  A `lin` or `aff` continuation is never dropped silently: `kTy`
at `lin`/`aff` is a thunk, and no `forget` constant has a thunk type.  An `unr` continuation can be
forgotten (`forgetBang`), but it holds no resource (`contShare`'s `unr` conjunct), and the end
state's typing pin has no resuming `unr` operation.

* **P8.a, the resource half (OQ-50 (c))**: on every complete run, every cell a captured
  continuation holds is released exactly once.  Not a separate property: it is T1's
  `ReleasedOnceAll` read at the runs that capture a continuation (`P8a` below names that reading),
  with `Final`'s empty memory at their end.
* **P8.b, the use count** (named-only, beside done): each continuation a step creates (`hop`) is
  used (applied to `inj₁ ()` or `inj₂ ()`) as its qualifier says.  The machine does not observe a
  continuation's use (`κ` is a λ-value, and two copies of it are indistinguishable from one), so
  the statement needs that observation, and how to make it is OQ-50, the user's choice: (a) an
  instrumented machine whose `hop` tags the `κ` it creates, Tang et al.'s Thm 3.6 shape
  ("ℒ(M) ∪ S = ℒ(N) ∪ T"); or (b) the TR's one-shot-cell machine, where `κ` is a heap cell freed by
  its use and P8.b is D9 at that cell.  Until OQ-50 is answered, `ContUse` is a placeholder name,
  not a target.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets

/-- **P8.a**: `ReleasedOnceAll` itself, read at the runs that capture a continuation. -/
abbrev P8a (J : TypingJ) : Prop := ReleasedOnceAll (ℍ := ℍ) J

end Targets

end
