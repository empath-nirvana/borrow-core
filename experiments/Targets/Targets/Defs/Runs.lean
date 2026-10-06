import Core.Stdio
import Targets.Defs.Effects

/-!
# Targets — runs, platforms, safety and release (DESIGN §2, D5–D9)

* **D5.** The platform answers, at the top, the operations no handler catches: a runner (a
  comodel, Ahman–Bauer Def. 1) with state-access semantics only.  It never touches the program's
  memory; allocation stays a machine step, quantified over every allocator by `Step1`.
* **D6.** Runs under a platform (`PStep`), first-order data (`VTy.Data`, `DataVal`), final
  configurations, and the runtime's outermost driver of a program that returns a loop (`RStep`).
* **D7.** Where a run may stop: at an operation of the row (`StopsIn`).
* **D8.** Every-run safety (`SafeRuns`), termination (`Terminates`), a safely driven loop
  (`SafeDrive`), and the answers whose programs terminate (`DivFree`).
* **D9.** A run as the list of its configurations (`PRun`), and release exactly once on runs that
  reuse no location (`ReleasedOnce`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload)

end Targets

namespace BoCa.Fig16.LogRel.Core

/-! ### D6. First-order data -/

/-- First-order data at `k` bound variables: `1`, `0`, integers, `⊗`, `⊕`, and `μX. A` over these.
No location, no code, no capability. -/
inductive VTy.DataB : Nat → VTy → Prop
  | unit (k) : VTy.DataB k .unit
  | zero (k) : VTy.DataB k .zero
  | int (k w) : VTy.DataB k (.int w)
  | tvar {k n} : n < k → VTy.DataB k (.tvar n)
  | tensor {k A B} : VTy.DataB k A → VTy.DataB k B → VTy.DataB k (.tensor A B)
  | sum {k A B} : VTy.DataB k A → VTy.DataB k B → VTy.DataB k (.sum A B)
  | mu {k A} : VTy.DataB (k + 1) A → VTy.DataB k (.mu A)

/-- A closed data type. -/
def VTy.Data (A : VTy) : Prop := VTy.DataB 0 A

end BoCa.Fig16.LogRel.Core

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload)

/-- The values of a closed data type (`BytesV`'s shape, `Core/Stdio.lean`): the least fixed point,
with `μ` read at its unrolling. -/
inductive DataVal : VTy → Val → Prop
  | unit : DataVal .unit .unit
  | int {w v} : v.IsInt w → DataVal (.int w) v
  | pair {A B v₁ v₂} : DataVal A v₁ → DataVal B v₂ → DataVal (.tensor A B) (Val.pair v₁ v₂)
  | inj₁ {A B v} : DataVal A v → DataVal (.sum A B) (Val.inj₁ v)
  | inj₂ {A B v} : DataVal B v → DataVal (.sum A B) (Val.inj₂ v)
  | roll {A v} : DataVal (VTy.inst (.mu A) A) v → DataVal (.mu A) v

/-! ### D5. The platform: a comodel -/

/-- A platform: the operations it answers, its state, and a co-operation per operation. -/
structure Platform where
  ops : Row
  St  : Type
  s₀  : St
  co  : St → UInt32 → UInt32 → Val → Option (Val × St)

/-- The protocol: data operations that resume once; every well-formed request answered; answers at
the operation's answer type. -/
structure Platform.Respects (P : Platform) : Prop where
  uniq  : P.ops.Uniq
  nz    : P.ops.NZ
  lin   : ∀ o ∈ P.ops, o.q = .lin ∧ o.abort = false
  data  : ∀ o ∈ P.ops, o.A.Data ∧ o.B.Data
  total : ∀ s o v, o ∈ P.ops → DataVal o.A v → ∃ w s', P.co s o.n o.i v = some (w, s')
  typed : ∀ s s' o v w, o ∈ P.ops → DataVal o.A v → P.co s o.n o.i v = some (w, s') →
            DataVal o.B w

/-- The platform with no operation. -/
def Platform.none : Platform := ⟨[], Unit, (), fun _ _ _ _ => Option.none⟩

/-! ### D6. Runs and the outermost driver -/

/-- A configuration under a platform: memory, term, platform state. -/
structure Conf (P : Platform) where
  μ : Heap
  e : Expr
  s : P.St

/-- A step under a platform: a machine step (`Step1`: every allocator's choice), or the platform
answering an operation of its row that no handler of the program catches. -/
inductive PStep (P : Platform) : Conf P → Conf P → Prop
  | mach {μ μ' : Heap} {e e' : Expr} {s : P.St} :
      Step1 (ℍ := ℍ) μ e μ' e' → PStep P ⟨μ, e, s⟩ ⟨μ', e', s⟩
  | plat {μ : Heap} {s s' : P.St} {K : Kont} {n i : UInt32} {v w : Val} {o : OpSig} :
      K.HasHnd n = false → Row.find P.ops n i = some o →
      P.co s n i v = some (w, s') →
      PStep P ⟨μ, K.plug (performE (.val (opPayload n i v))), s⟩ ⟨μ, K.plug (.val w), s'⟩

/-- Runs under a platform. -/
abbrev PSteps (P : Platform) := Relation.ReflTransGen (PStep (ℍ := ℍ) P)

/-- The initial configuration: the empty memory and the platform's initial state. -/
def init (P : Platform) (e : Expr) : Conf P := ⟨Adequacy.emptyMem, e, P.s₀⟩

/-- Final: a value of the data answer type, with the memory empty. -/
def Final (P : Platform) (A : VTy) (c : Conf P) : Prop :=
  ∃ v, c.e = .val v ∧ DataVal A v ∧ c.μ = Adequacy.emptyMem

/-- The phase of the outermost driver. -/
inductive Phase
  | main
  | drive
  deriving DecidableEq, Repr

/-- `next` of a loop thunk: its first observation (`forceE` at `ν` is the value itself). -/
def nextE (l : Val) : Expr := .app (.val l) (.val (Val.inj₁ .unit))

/-- The runtime drives a `main` that returns a loop until it finishes; it never closes it
(SPEC §11, §14). -/
inductive RStep (P : Platform) : Conf P × Phase → Conf P × Phase → Prop
  | run   {c c' : Conf P} {ph : Phase} : PStep (ℍ := ℍ) P c c' → RStep P (c, ph) (c', ph)
  | start {μ : Heap} {s : P.St} {l : Val} :
      RStep P (⟨μ, .val l, s⟩, .main) (⟨μ, nextE l, s⟩, .drive)
  | again {μ : Heap} {s : P.St} {l : Val} :
      RStep P (⟨μ, .val (Val.inj₂ l), s⟩, .drive) (⟨μ, nextE l, s⟩, .drive)

/-- A finished drive: the loop's answer, data, with the memory empty. -/
def FinalDrive (P : Platform) (A : VTy) : Conf P × Phase → Prop
  | (c, .drive) => ∃ a, c.e = .val (Val.inj₁ a) ∧ DataVal A a ∧ c.μ = Adequacy.emptyMem
  | (_, .main)  => False

/-! ### D7. Effect safety: where a run may stop -/

/-- A stop at an operation of the row `S`: a `perform` that no handler of its name catches, or a
`raise` that no frame catches, of an operation `S` has, of the matching kind. -/
def StopsIn (S : Row) (e : Expr) : Prop :=
  (∃ K n i v o, e = Kont.plug K (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
      Row.find S n i = some o ∧ o.abort = false) ∨
  (∃ K n i v o, e = Kont.plug K (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
      Row.find S n i = some o ∧ o.abort = true)

/-! ### D8. Safety, termination, divergence -/

/-- Every-run safety: no run gets stuck; a run that cannot step is final. -/
def SafeRuns (P : Platform) (A : VTy) (e : Expr) : Prop :=
  ∀ c, PSteps (ℍ := ℍ) P (init P e) c → Final P A c ∨ ∃ c', PStep (ℍ := ℍ) P c c'

/-- Termination: every run continues to a final configuration, and no run is infinite. -/
def Terminates (P : Platform) (A : VTy) (e : Expr) : Prop :=
  (∀ c, PSteps (ℍ := ℍ) P (init P e) c → ∃ c', PSteps (ℍ := ℍ) P c c' ∧ Final P A c') ∧
  ¬ ∃ f : ℕ → Conf P, f 0 = init P e ∧ ∀ n, PStep (ℍ := ℍ) P (f n) (f (n + 1))

/-- A driven loop: every finite prefix of the (possibly infinite) drive is safe. -/
def SafeDrive (P : Platform) (A : VTy) (e : Expr) : Prop :=
  ∀ rc, Relation.ReflTransGen (RStep (ℍ := ℍ) P) (init P e, .main) rc →
    FinalDrive P A rc ∨ ∃ rc', RStep (ℍ := ℍ) P rc rc'

/-- The answers whose programs terminate.  Divergence lives in `Loop` codata (decision 35), so
every `F_S A` at a data `A` is div-free; if divergence moved into rows, this predicate changes, and
the targets that read it with it. -/
def DivFree (_S : Row) (A : VTy) : Prop := A.Data

/-! ### D9. Finalisation exactly once -/

/-- A run, as the list of its configurations. -/
inductive PRun (P : Platform) : List (Conf P) → Prop
  | one (c : Conf P) : PRun P [c]
  | cons {c c' : Conf P} {cs : List (Conf P)} : PStep (ℍ := ℍ) P c c' → PRun P (c' :: cs) →
      PRun P (c :: c' :: cs)

/-- The run allocates `ℓ` at its `k`-th step. -/
def Allocated {P : Platform} (cs : List (Conf P)) (k : Nat) (ℓ : Loc) : Prop :=
  ∃ c c', cs[k]? = some c ∧ cs[k + 1]? = some c' ∧ c.μ ℓ = none ∧ (c'.μ ℓ).isSome

/-- The run releases `ℓ` at its `k`-th step. -/
def Released {P : Platform} (cs : List (Conf P)) (k : Nat) (ℓ : Loc) : Prop :=
  ∃ c c', cs[k]? = some c ∧ cs[k + 1]? = some c' ∧ (c.μ ℓ).isSome ∧ c'.μ ℓ = none

/-- The run never allocates a location it released earlier. -/
def NoReuse {P : Platform} (cs : List (Conf P)) : Prop :=
  ∀ j k ℓ, j < k → Released cs j ℓ → ¬ Allocated cs k ℓ

/-- Every location the run allocates is released exactly once, and none is released that the run
did not allocate. -/
def ReleasedOnce {P : Platform} (cs : List (Conf P)) : Prop :=
  (∀ ℓ k, Allocated cs k ℓ → ∃! j, Released cs j ℓ) ∧
  (∀ ℓ j, Released cs j ℓ → ∃ k, k < j ∧ Allocated cs k ℓ)

end Targets

end
