import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Backend2.Syntax

/-!
# #670 — a declarative linearity judgment for the LIR

`Lin p D B Γ t Δ B'` reads: with the variables `B` bound so far in the program and the variables
`Γ` owned, the term `t` consumes its operands, and leaves `Δ` owned after its value is consumed by
its context (`none` on a path that ends at `absurd`), having bound the variables `B'`.

The rules are those of the LIR's prose contract (`Backend2/Syntax.lean`):

- every variable is bound once in the program (`x ∉ B` at each binder) and has a type;
- each owned variable is consumed exactly once on every path: an operation, `drop`, or being the
  term's value consumes it, `copy` keeps it;
- both arms of a `case` leave the same set (`Join`); a path that ends at `absurd` is exempt;
- `copy x x'` needs `D x`, the variable's value duplicable;
- a function ends with everything consumed (`FnOK`).

`D` is a parameter. The LIR's types erase `!` (`Backend2/Types.lean`): a closure of `!U C` and one
of `U C` are both `thunk`, so duplicability is not a function of `LTy`. It is a fact about the
kernel type the variable was introduced at; the conversion's lemmas discharge it from the masks
(`Spike670/Slice1.lean`, `splitCtx_copies`). `Backend2/Lint.lean` does not check it: its soundness
is stated at `D = ⊤` (`Spike670/LintSound.lean`).

`LinL` is the same judgment without the program-wide bound set: freshness is then a separate
fact about the binders (`bnd`), which is how the conversion establishes it (fresh variables from a
counter). `LinL.toLin` turns one into the other.
-/

namespace Backend2.Spike670
open Backend2

/-- The leftovers of a `case`: the arms' when both return, the returning arm's when one ends at
`absurd`. -/
def Join : Option (Finset Var) → Option (Finset Var) → Option (Finset Var) → Prop
  | none, l, r => r = l
  | some a, none, r => r = some a
  | some a, some b, r => a = b ∧ r = some a

/-- `xs` consumed from `Γ` in order, each owned when it is used: `Γ'` is what is left. -/
inductive UseAll : Finset Var → List Var → Finset Var → Prop where
  | nil {Γ} : UseAll Γ [] Γ
  | cons {Γ x xs Γ'} : x ∈ Γ → UseAll (Γ.erase x) xs Γ' → UseAll Γ (x :: xs) Γ'

/-- The variables an operand-only form consumes. -/
def operands : Tm → Option (List Var)
  | .var x => some [x]
  | .unit | .lit _ => some []
  | .pair a b => some [a, b]
  | .inj _ a => some [a]
  | .clos _ xs => some xs
  | .app f a => some [f, a]
  | .app0 f | .sel f _ => some [f]
  | .call _ as | .prim _ as => some as
  | _ => none

section
variable (p : Prog) (D : Var → Prop)

/-- The variable has a type in the program. -/
def Typed (x : Var) : Prop := p.ty.contains x = true

/-- The arity facts `Lint` checks at a closure and a call. -/
def AritiesOK : Tm → Prop
  | .clos c xs => ∃ code, p.codes[c]? = some code ∧ ∀ fn ∈ code.fns, ∃ d, p.fns[fn]? = some d ∧
      (if code.kind == .lam then d.params.length - 1 else d.params.length) = xs.length
  | .call fn as => ∃ d, p.fns[fn]? = some d ∧ d.params.length = as.length
  | _ => True

/-- **The linearity judgment**, threaded through the program's bound variables. -/
inductive Lin : Finset Var → Finset Var → Tm → Option (Finset Var) → Finset Var → Prop where
  /-- A form that only consumes its operands. -/
  | ops {B Γ t xs Γ'} : operands t = some xs → AritiesOK p t → UseAll Γ xs Γ' →
      Lin B Γ t (some Γ') B
  | letvNone {B Γ x e b B₁} : Lin B Γ e none B₁ → Lin B Γ (.letv x e b) none B₁
  | letv {B Γ x e b Γ₁ B₁ Δ B₂} : Lin B Γ e (some Γ₁) B₁ → x ∉ B₁ → Typed p x →
      Lin (insert x B₁) (insert x Γ₁) b Δ B₂ → Lin B Γ (.letv x e b) Δ B₂
  | letpair {B Γ x y q b Δ B'} : q ∈ Γ → x ∉ B → Typed p x → y ∉ insert x B → Typed p y →
      Lin (insert y (insert x B)) (insert y (insert x (Γ.erase q))) b Δ B' →
      Lin B Γ (.letpair x y q b) Δ B'
  | case {B Γ s x b₁ y b₂ Δ₁ B₁ Δ₂ B₂ Δ} : s ∈ Γ → x ∉ B → Typed p x →
      Lin (insert x B) (insert x (Γ.erase s)) b₁ Δ₁ B₁ → y ∉ B₁ → Typed p y →
      Lin (insert y B₁) (insert y (Γ.erase s)) b₂ Δ₂ B₂ → Join Δ₁ Δ₂ Δ →
      Lin B Γ (.case s x b₁ y b₂) Δ B₂
  | absurd {B Γ s} : s ∈ Γ → Lin B Γ (.absurd s) none B
  | copy {B Γ x x' b Δ B'} : x ∈ Γ → D x → x' ∉ B → Typed p x' →
      Lin (insert x' B) (insert x' Γ) b Δ B' → Lin B Γ (.copy x x' b) Δ B'
  | drop {B Γ x b Δ B'} : x ∈ Γ → Lin B (Γ.erase x) b Δ B' → Lin B Γ (.drop x b) Δ B'

/-- A path's leftovers are fully consumed, or the path is unreachable. -/
def Closed (Δ : Option (Finset Var)) : Prop := Δ = none ∨ Δ = some ∅

/-- Parameters bound in order, each new and typed. -/
inductive ParamsOK : Finset Var → List Var → Finset Var → Prop where
  | nil {B} : ParamsOK B [] B
  | cons {B x xs B'} : x ∉ B → Typed p x → ParamsOK (insert x B) xs B' → ParamsOK B (x :: xs) B'

/-- A function: its parameters bound, its body ends with everything consumed. -/
def FnOK (B : Finset Var) (d : Fn) (B' : Finset Var) : Prop :=
  ∃ B₀ Δ, ParamsOK p B d.params B₀ ∧ Lin p D B₀ d.params.toFinset d.body Δ B' ∧ Closed Δ

/-- The functions in order, the bound set threaded through. -/
inductive FnsOK : Finset Var → List Fn → Finset Var → Prop where
  | nil {B} : FnsOK B [] B
  | cons {B d ds B₁ B₂} : FnOK p D B d B₁ → FnsOK B₁ ds B₂ → FnsOK B (d :: ds) B₂

/-- **A linear program** at the duplicability predicate `D`. -/
def LinOK : Prop :=
  ∃ B₁ Δ B₂, FnsOK p D ∅ p.fns.toList B₁ ∧ Lin p D B₁ ∅ p.main Δ B₂ ∧ Closed Δ

end

/-! ### The judgment without the bound set -/

/-- The variables a term binds, every one, in syntactic order. -/
def bnd : Tm → List Var
  | .letv x e b => x :: (bnd e ++ bnd b)
  | .letpair x y _ b => x :: y :: bnd b
  | .case _ x b₁ y b₂ => x :: (bnd b₁ ++ y :: bnd b₂)
  | .copy _ x' b => x' :: bnd b
  | .drop _ b => bnd b
  | _ => []

/-- **Linearity without the bound set**: the same rules, freshness left to the binders. -/
inductive LinL (D : Var → Prop) : Finset Var → Tm → Option (Finset Var) → Prop where
  | ops {Γ t xs Γ'} : operands t = some xs → UseAll Γ xs Γ' → LinL D Γ t (some Γ')
  | letvNone {Γ x e b} : LinL D Γ e none → LinL D Γ (.letv x e b) none
  | letv {Γ x e b Γ₁ Δ} : LinL D Γ e (some Γ₁) → LinL D (insert x Γ₁) b Δ →
      LinL D Γ (.letv x e b) Δ
  | letpair {Γ x y q b Δ} : q ∈ Γ → LinL D (insert y (insert x (Γ.erase q))) b Δ →
      LinL D Γ (.letpair x y q b) Δ
  | case {Γ s x b₁ y b₂ Δ₁ Δ₂ Δ} : s ∈ Γ → LinL D (insert x (Γ.erase s)) b₁ Δ₁ →
      LinL D (insert y (Γ.erase s)) b₂ Δ₂ → Join Δ₁ Δ₂ Δ → LinL D Γ (.case s x b₁ y b₂) Δ
  | absurd {Γ s} : s ∈ Γ → LinL D Γ (.absurd s) none
  | copy {Γ x x' b Δ} : x ∈ Γ → D x → LinL D (insert x' Γ) b Δ → LinL D Γ (.copy x x' b) Δ
  | drop {Γ x b Δ} : x ∈ Γ → LinL D (Γ.erase x) b Δ → LinL D Γ (.drop x b) Δ

end Backend2.Spike670
