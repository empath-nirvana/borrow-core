import Mathlib.Data.Fintype.Pi

/-!
# Grades — the interval semiring over `{0, 1, ∞}`

A grade is an interval `[lo, hi]` of use counts.  The endpoints are `0`, `1` and `∞`; the lower
endpoint is `0` or `1` ("at least once" is all a lower bound records), so there are five grades:

| grade | interval | meaning |
|---|---|---|
| `erased` | `[0,0]` | never used at run time |
| `linear` | `[1,1]` | exactly once |
| `affine` | `[0,1]` | at most once |
| `relevant` | `[1,∞]` | at least once |
| `unrestricted` | `[0,∞]` | any number of times |

`+` and `·` act on the endpoints, with `1 + 1` saturating to `∞` at the upper endpoint and to `1`
at the lower one (a lower bound of two uses is a lower bound of one).  The order is containment.
Every law is decided by computation over the five grades.
-/

namespace Grades

/-- An endpoint: `0`, `1` or `∞`. -/
inductive End where
  | zero | one | inf
  deriving DecidableEq, Repr

instance : Fintype End where
  elems := ⟨{.zero, .one, .inf}, by decide⟩
  complete x := by cases x <;> decide

namespace End

def add : End → End → End
  | .zero, b => b
  | a, .zero => a
  | _, _ => .inf

def mul : End → End → End
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, b => b
  | a, .one => a
  | .inf, .inf => .inf

/-- `0 ≤ 1 ≤ ∞`. -/
def le : End → End → Bool
  | .zero, _ => true
  | .one, .zero => false
  | .one, _ => true
  | .inf, .inf => true
  | .inf, _ => false

end End

/-- The five intervals. -/
inductive Grade where
  | erased | linear | affine | relevant | unrestricted
  deriving DecidableEq, Repr

instance : Fintype Grade where
  elems := ⟨{.erased, .linear, .affine, .relevant, .unrestricted}, by decide⟩
  complete x := by cases x <;> decide

namespace Grade

def lo : Grade → End
  | .erased => .zero | .linear => .one | .affine => .zero
  | .relevant => .one | .unrestricted => .zero

def hi : Grade → End
  | .erased => .zero | .linear => .one | .affine => .one
  | .relevant => .inf | .unrestricted => .inf

/-- The interval with the given endpoints; a lower endpoint above `1` is read as `1`, and an
upper endpoint below the lower one does not arise from `+` or `·` of grades. -/
def ofEnds : End → End → Grade
  | .zero, .zero => .erased
  | .zero, .one => .affine
  | .zero, .inf => .unrestricted
  | _, .zero => .erased
  | _, .one => .linear
  | _, .inf => .relevant

def add (a b : Grade) : Grade := ofEnds (a.lo.add b.lo) (a.hi.add b.hi)
def mul (a b : Grade) : Grade := ofEnds (a.lo.mul b.lo) (a.hi.mul b.hi)

instance : Add Grade := ⟨add⟩
instance : Mul Grade := ⟨mul⟩
instance : Zero Grade := ⟨.erased⟩
instance : One Grade := ⟨.linear⟩

/-- `ω = [0,∞]`. -/
abbrev ω : Grade := .unrestricted

/-- Containment: `[a,b] ≤ [c,d]` iff `c ≤ a` and `b ≤ d`. -/
def le (a b : Grade) : Bool := b.lo.le a.lo && a.hi.le b.hi

instance : LE Grade := ⟨fun a b => le a b = true⟩
instance (a b : Grade) : Decidable (a ≤ b) := inferInstanceAs (Decidable (le a b = true))

/-- The slot is present at run time: the grade is not `[0,0]`. -/
def live (g : Grade) : Bool := g != .erased

/-- The grade allows the slot to be dropped: its lower endpoint is `0`. -/
def droppable (g : Grade) : Bool := g.lo == .zero

/-- The grade allows the slot to be used more than once: its upper endpoint is `∞`. -/
def copyable (g : Grade) : Bool := g.hi == .inf

/-- The endpoint type conditions, for a type whose droppability is `f` and persistence `p`:
a droppable grade other than `[0,0]` asks for a forgettable type, and a copyable grade for a
persistent one. -/
def ok (g : Grade) (f p : Bool) : Bool :=
  (!(g.droppable && g.live) || f) && (!g.copyable || p)

/-! ### The laws, by computation -/

theorem add_comm : ∀ a b : Grade, a + b = b + a := by decide
theorem add_assoc : ∀ a b c : Grade, a + b + c = a + (b + c) := by decide
theorem zero_add : ∀ a : Grade, 0 + a = a := by decide
theorem add_zero : ∀ a : Grade, a + 0 = a := by decide
theorem mul_assoc : ∀ a b c : Grade, a * b * c = a * (b * c) := by decide
theorem one_mul : ∀ a : Grade, 1 * a = a := by decide
theorem mul_one : ∀ a : Grade, a * 1 = a := by decide
theorem zero_mul : ∀ a : Grade, 0 * a = 0 := by decide
theorem mul_zero : ∀ a : Grade, a * 0 = 0 := by decide
theorem left_distrib : ∀ a b c : Grade, a * (b + c) = a * b + a * c := by decide
theorem right_distrib : ∀ a b c : Grade, (a + b) * c = a * c + b * c := by decide
theorem mul_comm : ∀ a b : Grade, a * b = b * a := by decide

theorem le_refl : ∀ a : Grade, a ≤ a := by decide
theorem le_trans : ∀ a b c : Grade, a ≤ b → b ≤ c → a ≤ c := by decide
theorem le_antisymm : ∀ a b : Grade, a ≤ b → b ≤ a → a = b := by decide
theorem add_le_add : ∀ a b c d : Grade, a ≤ b → c ≤ d → a + c ≤ b + d := by decide
theorem mul_le_mul : ∀ a b c d : Grade, a ≤ b → c ≤ d → a * c ≤ b * d := by decide

/-- The order the issue names: `linear ≤ affine ≤ unrestricted`, `erased ≤ affine`,
`linear ≤ relevant ≤ unrestricted`, and `erased`, `linear` incomparable. -/
theorem order_facts :
    linear ≤ affine ∧ affine ≤ unrestricted ∧ erased ≤ affine ∧ linear ≤ relevant ∧
      relevant ≤ unrestricted ∧ ¬ erased ≤ linear ∧ ¬ linear ≤ erased := by decide

/-! ### Liveness, splitting and scaling -/

/-- A sum is live iff a summand is. -/
theorem live_add : ∀ a b : Grade, (a + b).live = (a.live || b.live) := by decide

/-- Both summands live: the sum is copyable. -/
theorem copyable_add : ∀ a b : Grade, a.live → b.live → (a + b).copyable := by decide

/-- `ω · g` is dead exactly when `g` is. -/
theorem live_ω_mul : ∀ a : Grade, (ω * a).live = a.live := by decide

/-- `ω · g` is copyable and droppable when live. -/
theorem ω_mul_live : ∀ a : Grade, a.live → ω * a = ω := by decide

/-- A live grade contains `1`: it allows one use. -/
theorem live_iff_one_le : ∀ a : Grade, a.live ↔ (a.lo.le .one && End.le .one a.hi) := by decide

/-- The type conditions pass to the summands, when persistent types are forgettable. -/
theorem ok_add : ∀ a b : Grade, ∀ f p : Bool, (p → f) → (a + b).ok f p → a.ok f p ∧ b.ok f p := by
  decide

/-- A live grade that is not droppable nor copyable is `linear`. -/
theorem ok_false_false : ∀ a : Grade, a.ok false false → a = .erased ∨ a = .linear := by decide

end Grade

end Grades
