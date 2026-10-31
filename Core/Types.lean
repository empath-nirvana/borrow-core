import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Support.Lifetimes.Substitution
import Support.LogicalRelation.Facts
import Support.Statics.Contexts
import Core.Opaque

/-!
# Core — Types  `[spec §3, §6, §7]`

Call-by-push-value types, the index of the typed world's records.

* Value types `VTy ::= 1 | A ⊗ B | 0 | A ⊕ B | U C | Ref A | Imm @a A | Mut @a A | [@a] A | !A | Unk`.
* Computation types `CTy ::= F A | A ⊸ C | C & D | ⊤ | ∀'x ⊏ @b. C | νX. C`.  In `νX. C` the
  value type `U X` is the type variable `0` of `C`'s value types (`Nu.lean`); the delay, stream
  and finite iterator types are abbreviations over it.

`VTy.recV` is the value-type eliminator with `U C` a leaf: the typed world never looks inside
a computation type.  Beside the formers: the free lifetime variables `VFree`/`CFree`, the
reborrow metafunction `Imm̲` (`VTy.immReborrow`), capture-avoiding lifetime substitution
(`VTy.applyLSub`/`CTy.applyLSub`, `CTy.instLife`), the outlives judgment `VOutlives` and
scoping `VScoped`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar LSubst)

/-- The structural qualifier of a control operation's continuation: `lin`, must resume (resumed
exactly once); `cancel`, cancellable (resumed at most once, or cancelled); `unr`, unrestricted
(resumed any number of times, or cancelled). At `lin` and `cancel` the continuation is a linear
value.  `[spec §19]` -/
inductive Qual where
  | lin
  | cancel
  | unr
  deriving DecidableEq, Repr

mutual
/-- Value types.  `[spec §3]` -/
inductive VTy where
  | unit
  | tensor (A B : VTy)
  | zero
  | sum (A B : VTy)
  /-- `U C`. -/
  | thunk (C : CTy)
  /-- `Ref A`. -/
  | ref (A : VTy)
  /-- `Imm @a A`. -/
  | imm (a : Lifetime.Life) (A : VTy)
  /-- `Mut @a A`. -/
  | mut (a : Lifetime.Life) (A : VTy)
  /-- `[@a] A`. -/
  | box (a : Lifetime.Life) (A : VTy)
  /-- `!A`. -/
  | bang (A : VTy)
  /-- `Unk`. -/
  | unk
  /-- A type variable, de Bruijn. -/
  | tvar (n : Nat)
  /-- `μX. A`, binding index `0` in `A`. -/
  | mu (A : VTy)
  /-- `I32` (`w32`) and `I64` (`w64`): opaque integers, holding no resource.  `[spec §8]` -/
  | int (w : Width)
  /-- `[L]`: the run-time family `⊛_{i<n} L` of leaf places, a value `(ℓ, n)` whose `i`-th
  leaf is the location `ℓ + i`.  `Array A = [Ref A]`.  `[spec §9]` -/
  | fam (L : VTy)
  /-- An opaque host type (`Input`, `Output`): a leaf with no rule, whose relation is the model
  `k.Holds`.  `[spec §11]` -/
  | opq (k : Opaque)
/-- Computation types.  `[spec §3]` -/
inductive CTy where
  /-- `F A`. -/
  | ret (A : VTy)
  /-- `A ⊸ C`. -/
  | arr (A : VTy) (C : CTy)
  /-- `C & D`. -/
  | amp (C D : CTy)
  /-- `⊤`. -/
  | top
  /-- `∀'x ⊏ @b. C`. -/
  | all (x : LifeVar) (b : Lifetime.Life) (C : CTy)
  /-- `νX. C`: the greatest fixed point, with `U X` the type variable `0` in `C`.  `[spec §7]` -/
  | nu (C : CTy)
  /-- One operation of an effect row: `C` extended by the operation `i` of the name `n`,
  `A ↠^q B`, with its cancel row `fin`: what cancelling a continuation captured at the operation
  may raise or perform, `⊤` when it cannot be cancelled, otherwise the operations of `fin`'s layers
  (`CTy.rowOf`).  `rc` marks an operation cancelled by resuming it (`OpSig.rc`), read by typing
  only.  `F_Σ R` is a stack of these over `F R` (`CTy.effOf`).  `[spec §19, §27, §29a]` -/
  | eff (n i : UInt32) (q : Qual) (A B : VTy) (fin : CTy) (rc : Bool) (C : CTy)
end

/-- The value-type eliminator with `U C` a leaf. -/
@[elab_as_elim]
theorem VTy.recV {motive : VTy → Prop}
    (unit : motive .unit)
    (tensor : ∀ A B, motive A → motive B → motive (.tensor A B))
    (zero : motive .zero)
    (sum : ∀ A B, motive A → motive B → motive (.sum A B))
    (thunk : ∀ C, motive (.thunk C))
    (ref : ∀ A, motive A → motive (.ref A))
    (imm : ∀ a A, motive A → motive (.imm a A))
    («mut» : ∀ a A, motive A → motive (.mut a A))
    (box : ∀ a A, motive A → motive (.box a A))
    (bang : ∀ A, motive A → motive (.bang A))
    (unk : motive .unk)
    (tvar : ∀ n, motive (.tvar n))
    (mu : ∀ A, motive A → motive (.mu A))
    (int : ∀ w, motive (.int w))
    (fam : ∀ L, motive L → motive (.fam L))
    (opq : ∀ k, motive (.opq k)) : ∀ A, motive A
  | .unit => unit
  | .tensor A B => tensor A B (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk tvar mu int fam opq A)
      (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk tvar mu int fam opq B)
  | .zero => zero
  | .sum A B => sum A B (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk tvar mu int fam opq A)
      (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk tvar mu int fam opq B)
  | .thunk C => thunk C
  | .ref A => ref A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk tvar mu int fam opq A)
  | .imm a A => imm a A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk tvar mu int fam opq A)
  | .mut a A => «mut» a A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk tvar mu int fam opq A)
  | .box a A => box a A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk tvar mu int fam opq A)
  | .bang A => bang A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk tvar mu int fam opq A)
  | .fam A => fam A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk tvar mu int fam opq A)
  | .unk => unk
  | .int w => int w
  | .opq k => opq k
  | .tvar n => tvar n
  | .mu A => mu A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk tvar mu int fam opq A)

/-- `A` is `0`. -/
def VTy.isZero : VTy → Bool
  | .zero => true
  | _ => false

/-- `C` has no effect row anywhere a stack reaches: the stack semantics (`cC_iff_stacks`) is
`wpTS` at its end.  `[spec §19]` -/
def CTy.EffFree : CTy → Prop
  | .ret _ | .top => True
  | .arr _ C | .all _ _ C | .nu C => C.EffFree
  | .amp C D => C.EffFree ∧ D.EffFree
  | .eff _ _ _ _ _ _ _ _ => False

/-- An operation of an effect row: the operation `i` of the name `n`, `A ↠^q B`, and its cancel
row `fin` (`CTy.eff`), the empty row `F 1` by default.  `[spec §19, §27]` -/
structure OpSig where
  n : UInt32
  i : UInt32
  q : Qual
  A : VTy
  B : VTy
  fin : CTy := .ret .unit
  /-- The operation is cancelled by resuming it: the cancellable `await` of `[await-c]`, or the
  abortive `cancelled` it raises on the answer `inr ()`. Only `[await-c]` performs or raises a marked
  operation. Neither the relation nor the machine reads it.  `[spec §29a]` -/
  rc : Bool := false

/-- An operation `A ↠^q B` is capturable: not must-resume, and not abortive (its answer type is not
`0`), so a continuation captured at it has a cancel branch, and its cancel row is read.
`[spec §27]` -/
def capB (q : Qual) (B : VTy) : Bool := q != .lin && !B.isZero

theorem capB_congr {q : Qual} {B B' : VTy} (h : B.isZero = B'.isZero) : capB q B = capB q B' := by
  simp only [capB, h]

/-- `F_Σ R`: the row's operations stacked over `F R`; `F_∅ R = F R`.  `[spec §19]` -/
def CTy.effOf : List OpSig → VTy → CTy
  | [], R => .ret R
  | o :: os, R => .eff o.n o.i o.q o.A o.B o.fin o.rc (CTy.effOf os R)

/-- The operations a cancel row holds: its layers, `[]` at any other former.  `[spec §27]` -/
def CTy.rowOf : CTy → List OpSig
  | .eff n i q A B fin rc C => ⟨n, i, q, A, B, fin, rc⟩ :: CTy.rowOf C
  | _ => []

/-- The cancel row `⊤`: a continuation captured there cannot be cancelled.  `[spec §27]` -/
def CTy.isTop : CTy → Bool
  | .top => true
  | _ => false

theorem CTy.rowOf_effOf : ∀ (S : List OpSig) (R : VTy), (CTy.effOf S R).rowOf = S
  | [], _ => rfl
  | _ :: S, R => by simp only [CTy.effOf, CTy.rowOf, CTy.rowOf_effOf S R]

/-- `A ⊸ B` at value type: `U (A ⊸ F B)`, BoLo's arrow read call-by-value. -/
abbrev VTy.lolli (A B : VTy) : VTy := .thunk (.arr A (.ret B))

/-- `∀'x ⊏ @b. A` at value type: `U (∀'x ⊏ @b. F A)`, BoLo's `∀` read call-by-value. -/
abbrev VTy.all (x : LifeVar) (b : Lifetime.Life) (A : VTy) : VTy := .thunk (.all x b (.ret A))

/-! ### Free lifetime variables -/

mutual
/-- `'x` occurs free in `A`; `∀'y ⊏ @b. C` binds `'y` in `C` and not in `@b`. -/
def VFree (x : LifeVar) : VTy → Prop
  | .unit => False
  | .zero => False
  | .unk => False
  | .int _ => False
  | .opq _ => False
  | .tensor A B => VFree x A ∨ VFree x B
  | .sum A B => VFree x A ∨ VFree x B
  | .thunk C => CFree x C
  | .ref A => VFree x A
  | .bang A => VFree x A
  | .fam A => VFree x A
  | .imm a A => a.mentions x = true ∨ VFree x A
  | .mut a A => a.mentions x = true ∨ VFree x A
  | .box a A => a.mentions x = true ∨ VFree x A
  | .tvar _ => False
  | .mu A => VFree x A
/-- `'x` occurs free in `C`. -/
def CFree (x : LifeVar) : CTy → Prop
  | .ret A => VFree x A
  | .arr A C => VFree x A ∨ CFree x C
  | .amp C D => CFree x C ∨ CFree x D
  | .top => False
  | .all y b C => b.mentions x = true ∨ (x ≠ y ∧ CFree x C)
  | .nu C => CFree x C
  | .eff _ _ _ A B fin _ C => VFree x A ∨ VFree x B ∨ CFree x fin ∨ CFree x C
end

/-! ### Type variables: renaming, substitution, closedness

`U C` is a leaf: a type variable is never looked for inside a computation type.  The lemma
set is `experiments/Recursion/Recursion/ImmMu.lean`'s (`MTy`), at `VTy`. -/

namespace VTy

def upR (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => r n + 1

def rename (r : Nat → Nat) : VTy → VTy
  | .unit => .unit
  | .tensor A B => .tensor (rename r A) (rename r B)
  | .zero => .zero
  | .sum A B => .sum (rename r A) (rename r B)
  | .thunk C => .thunk C
  | .ref A => .ref (rename r A)
  | .imm a A => .imm a (rename r A)
  | .mut a A => .mut a (rename r A)
  | .box a A => .box a (rename r A)
  | .bang A => .bang (rename r A)
  | .fam A => .fam (rename r A)
  | .unk => .unk
  | .int w => .int w
  | .opq k => .opq k
  | .tvar n => .tvar (r n)
  | .mu A => .mu (rename (upR r) A)

/-- `x · f`: `0 ↦ x`, `n + 1 ↦ f n`. -/
def scons {α : Type} (x : α) (f : Nat → α) : Nat → α
  | 0 => x
  | n + 1 => f n

def upS (σ : Nat → VTy) : Nat → VTy := scons (.tvar 0) (fun n => rename Nat.succ (σ n))

def subst (σ : Nat → VTy) : VTy → VTy
  | .unit => .unit
  | .tensor A B => .tensor (subst σ A) (subst σ B)
  | .zero => .zero
  | .sum A B => .sum (subst σ A) (subst σ B)
  | .thunk C => .thunk C
  | .ref A => .ref (subst σ A)
  | .imm a A => .imm a (subst σ A)
  | .mut a A => .mut a (subst σ A)
  | .box a A => .box a (subst σ A)
  | .bang A => .bang (subst σ A)
  | .fam A => .fam (subst σ A)
  | .unk => .unk
  | .int w => .int w
  | .opq k => .opq k
  | .tvar n => σ n
  | .mu A => .mu (subst (upS σ) A)

/-- `T[S/X]`: index `0` to `S`, the others down by one. -/
def inst (S T : VTy) : VTy := subst (scons S .tvar) T

theorem rename_rename : ∀ (A : VTy) (r r' : Nat → Nat),
    rename r (rename r' A) = rename (r ∘ r') A
  | .unit, _, _ => rfl
  | .tensor A B, r, r' => by simp [rename, rename_rename A, rename_rename B]
  | .zero, _, _ => rfl
  | .sum A B, r, r' => by simp [rename, rename_rename A, rename_rename B]
  | .thunk _, _, _ => rfl
  | .ref A, r, r' => by simp [rename, rename_rename A]
  | .imm _ A, r, r' => by simp [rename, rename_rename A]
  | .mut _ A, r, r' => by simp [rename, rename_rename A]
  | .box _ A, r, r' => by simp [rename, rename_rename A]
  | .bang A, r, r' => by simp [rename, rename_rename A]
  | .fam A, r, r' => by simp [rename, rename_rename A]
  | .unk, _, _ => rfl
  | .int _, _, _ => rfl
  | .opq _, _, _ => rfl
  | .tvar _, _, _ => rfl
  | .mu A, r, r' => by
      simp only [rename, rename_rename A]
      congr 2
      funext n; cases n <;> rfl

theorem subst_rename : ∀ (A : VTy) (σ : Nat → VTy) (r : Nat → Nat),
    subst σ (rename r A) = subst (σ ∘ r) A
  | .unit, _, _ => rfl
  | .tensor A B, σ, r => by simp [rename, subst, subst_rename A, subst_rename B]
  | .zero, _, _ => rfl
  | .sum A B, σ, r => by simp [rename, subst, subst_rename A, subst_rename B]
  | .thunk _, _, _ => rfl
  | .ref A, σ, r => by simp [rename, subst, subst_rename A]
  | .imm _ A, σ, r => by simp [rename, subst, subst_rename A]
  | .mut _ A, σ, r => by simp [rename, subst, subst_rename A]
  | .box _ A, σ, r => by simp [rename, subst, subst_rename A]
  | .bang A, σ, r => by simp [rename, subst, subst_rename A]
  | .fam A, σ, r => by simp [rename, subst, subst_rename A]
  | .unk, _, _ => rfl
  | .int _, _, _ => rfl
  | .opq _, _, _ => rfl
  | .tvar _, _, _ => rfl
  | .mu A, σ, r => by
      simp only [rename, subst, subst_rename A]
      congr 2
      funext n; cases n <;> rfl

theorem rename_subst : ∀ (A : VTy) (r : Nat → Nat) (σ : Nat → VTy),
    rename r (subst σ A) = subst (fun n => rename r (σ n)) A
  | .unit, _, _ => rfl
  | .tensor A B, r, σ => by simp [rename, subst, rename_subst A, rename_subst B]
  | .zero, _, _ => rfl
  | .sum A B, r, σ => by simp [rename, subst, rename_subst A, rename_subst B]
  | .thunk _, _, _ => rfl
  | .ref A, r, σ => by simp [rename, subst, rename_subst A]
  | .imm _ A, r, σ => by simp [rename, subst, rename_subst A]
  | .mut _ A, r, σ => by simp [rename, subst, rename_subst A]
  | .box _ A, r, σ => by simp [rename, subst, rename_subst A]
  | .bang A, r, σ => by simp [rename, subst, rename_subst A]
  | .fam A, r, σ => by simp [rename, subst, rename_subst A]
  | .unk, _, _ => rfl
  | .int _, _, _ => rfl
  | .opq _, _, _ => rfl
  | .tvar _, _, _ => rfl
  | .mu A, r, σ => by
      simp only [rename, subst, rename_subst A]
      congr 2
      funext n
      cases n with
      | zero => rfl
      | succ n =>
          simp only [upS, scons, rename_rename]
          rfl

theorem subst_subst : ∀ (A : VTy) (σ τ : Nat → VTy),
    subst σ (subst τ A) = subst (fun n => subst σ (τ n)) A
  | .unit, _, _ => rfl
  | .tensor A B, σ, τ => by simp [subst, subst_subst A, subst_subst B]
  | .zero, _, _ => rfl
  | .sum A B, σ, τ => by simp [subst, subst_subst A, subst_subst B]
  | .thunk _, _, _ => rfl
  | .ref A, σ, τ => by simp [subst, subst_subst A]
  | .imm _ A, σ, τ => by simp [subst, subst_subst A]
  | .mut _ A, σ, τ => by simp [subst, subst_subst A]
  | .box _ A, σ, τ => by simp [subst, subst_subst A]
  | .bang A, σ, τ => by simp [subst, subst_subst A]
  | .fam A, σ, τ => by simp [subst, subst_subst A]
  | .unk, _, _ => rfl
  | .int _, _, _ => rfl
  | .opq _, _, _ => rfl
  | .tvar _, _, _ => rfl
  | .mu A, σ, τ => by
      simp only [subst, subst_subst A]
      congr 2
      funext n
      cases n with
      | zero => rfl
      | succ n =>
          simp only [upS, scons, subst_rename, rename_subst]
          rfl

/-- The identity substitution. -/
theorem subst_id : ∀ (A : VTy), subst .tvar A = A
  | .unit => rfl
  | .tensor A B => by simp [subst, subst_id A, subst_id B]
  | .zero => rfl
  | .sum A B => by simp [subst, subst_id A, subst_id B]
  | .thunk _ => rfl
  | .ref A => by simp [subst, subst_id A]
  | .imm _ A => by simp [subst, subst_id A]
  | .mut _ A => by simp [subst, subst_id A]
  | .box _ A => by simp [subst, subst_id A]
  | .bang A => by simp [subst, subst_id A]
  | .fam A => by simp [subst, subst_id A]
  | .unk => rfl
  | .int _ => rfl
  | .opq _ => rfl
  | .tvar _ => rfl
  | .mu A => by
      have : upS .tvar = .tvar := by
        funext n; cases n <;> rfl
      simp only [subst, this, subst_id A]

/-- Every free variable of `A` is below `k`. -/
def Cl : Nat → VTy → Prop
  | _, .unit => True
  | k, .tensor A B => Cl k A ∧ Cl k B
  | _, .zero => True
  | k, .sum A B => Cl k A ∧ Cl k B
  | _, .thunk _ => True
  | k, .ref A => Cl k A
  | k, .imm _ A => Cl k A
  | k, .mut _ A => Cl k A
  | k, .box _ A => Cl k A
  | k, .bang A => Cl k A
  | k, .fam A => Cl k A
  | _, .unk => True
  | _, .int _ => True
  | _, .opq _ => True
  | k, .tvar n => n < k
  | k, .mu A => Cl (k + 1) A

theorem Cl_rename : ∀ (A : VTy) {k k' : Nat} (r : Nat → Nat), Cl k A →
    (∀ n, n < k → r n < k') → Cl k' (rename r A)
  | .unit, _, _, _, _, _ => trivial
  | .tensor A B, _, _, r, h, hr => ⟨Cl_rename A r h.1 hr, Cl_rename B r h.2 hr⟩
  | .zero, _, _, _, _, _ => trivial
  | .sum A B, _, _, r, h, hr => ⟨Cl_rename A r h.1 hr, Cl_rename B r h.2 hr⟩
  | .thunk _, _, _, _, _, _ => trivial
  | .ref A, _, _, r, h, hr => Cl_rename A r h hr
  | .imm _ A, _, _, r, h, hr => Cl_rename A r h hr
  | .mut _ A, _, _, r, h, hr => Cl_rename A r h hr
  | .box _ A, _, _, r, h, hr => Cl_rename A r h hr
  | .bang A, _, _, r, h, hr => Cl_rename A r h hr
  | .fam A, _, _, r, h, hr => Cl_rename A r h hr
  | .unk, _, _, _, _, _ => trivial
  | .int _, _, _, _, _, _ => trivial
  | .opq _, _, _, _, _, _ => trivial
  | .tvar n, _, _, _, h, hr => hr n h
  | .mu A, _, _, r, h, hr => Cl_rename A (upR r) h (fun n hn => by
      cases n with
      | zero => exact Nat.succ_pos _
      | succ n => exact Nat.succ_lt_succ (hr n (Nat.lt_of_succ_lt_succ hn)))

theorem Cl_substB : ∀ (A : VTy) {k j : Nat} (σ : Nat → VTy), Cl j A → (∀ n, n < j → Cl k (σ n)) →
    Cl k (subst σ A)
  | .unit, _, _, _, _, _ => trivial
  | .tensor A B, _, _, σ, hA, h => ⟨Cl_substB A σ hA.1 h, Cl_substB B σ hA.2 h⟩
  | .zero, _, _, _, _, _ => trivial
  | .sum A B, _, _, σ, hA, h => ⟨Cl_substB A σ hA.1 h, Cl_substB B σ hA.2 h⟩
  | .thunk _, _, _, _, _, _ => trivial
  | .ref A, _, _, σ, hA, h => Cl_substB A σ hA h
  | .imm _ A, _, _, σ, hA, h => Cl_substB A σ hA h
  | .mut _ A, _, _, σ, hA, h => Cl_substB A σ hA h
  | .box _ A, _, _, σ, hA, h => Cl_substB A σ hA h
  | .bang A, _, _, σ, hA, h => Cl_substB A σ hA h
  | .fam A, _, _, σ, hA, h => Cl_substB A σ hA h
  | .unk, _, _, _, _, _ => trivial
  | .int _, _, _, _, _, _ => trivial
  | .opq _, _, _, _, _, _ => trivial
  | .tvar n, _, _, _, hA, h => h n hA
  | .mu A, k, _, σ, hA, h => Cl_substB A (upS σ) hA (fun n hn => by
      cases n with
      | zero => exact Nat.succ_pos k
      | succ n =>
          exact Cl_rename (σ n) Nat.succ (h n (Nat.lt_of_succ_lt_succ hn))
            (fun _ hm => Nat.succ_lt_succ hm))

theorem Cl_subst : ∀ (A : VTy) {k : Nat} (σ : Nat → VTy), (∀ n, Cl k (σ n)) →
    Cl k (subst σ A)
  | .unit, _, _, _ => trivial
  | .tensor A B, _, σ, h => ⟨Cl_subst A σ h, Cl_subst B σ h⟩
  | .zero, _, _, _ => trivial
  | .sum A B, _, σ, h => ⟨Cl_subst A σ h, Cl_subst B σ h⟩
  | .thunk _, _, _, _ => trivial
  | .ref A, _, σ, h => Cl_subst A σ h
  | .imm _ A, _, σ, h => Cl_subst A σ h
  | .mut _ A, _, σ, h => Cl_subst A σ h
  | .box _ A, _, σ, h => Cl_subst A σ h
  | .bang A, _, σ, h => Cl_subst A σ h
  | .fam A, _, σ, h => Cl_subst A σ h
  | .unk, _, _, _ => trivial
  | .int _, _, _, _ => trivial
  | .opq _, _, _, _ => trivial
  | .tvar n, _, _, h => h n
  | .mu A, k, σ, h => Cl_subst A (upS σ) (fun n => by
      cases n with
      | zero => exact Nat.succ_pos k
      | succ n => exact Cl_rename (σ n) Nat.succ (h n) (fun _ hm => Nat.succ_lt_succ hm))

theorem Cl_mono : ∀ (A : VTy) {k k' : Nat}, Cl k A → k ≤ k' → Cl k' A
  | .unit, _, _, _, _ => trivial
  | .tensor A B, _, _, h, hk => ⟨Cl_mono A h.1 hk, Cl_mono B h.2 hk⟩
  | .zero, _, _, _, _ => trivial
  | .sum A B, _, _, h, hk => ⟨Cl_mono A h.1 hk, Cl_mono B h.2 hk⟩
  | .thunk _, _, _, _, _ => trivial
  | .ref A, _, _, h, hk => Cl_mono A h hk
  | .imm _ A, _, _, h, hk => Cl_mono A h hk
  | .mut _ A, _, _, h, hk => Cl_mono A h hk
  | .box _ A, _, _, h, hk => Cl_mono A h hk
  | .bang A, _, _, h, hk => Cl_mono A h hk
  | .fam A, _, _, h, hk => Cl_mono A h hk
  | .unk, _, _, _, _ => trivial
  | .int _, _, _, _, _ => trivial
  | .opq _, _, _, _, _ => trivial
  | .tvar _, _, _, h, hk => Nat.lt_of_lt_of_le h hk
  | .mu A, _, _, h, hk => Cl_mono A h (Nat.succ_le_succ hk)

theorem rename_closed : ∀ (A : VTy) {k : Nat} (r : Nat → Nat), Cl k A →
    (∀ n, n < k → r n = n) → rename r A = A
  | .unit, _, _, _, _ => rfl
  | .tensor A B, _, r, h, hr => by simp [rename, rename_closed A r h.1 hr, rename_closed B r h.2 hr]
  | .zero, _, _, _, _ => rfl
  | .sum A B, _, r, h, hr => by simp [rename, rename_closed A r h.1 hr, rename_closed B r h.2 hr]
  | .thunk _, _, _, _, _ => rfl
  | .ref A, _, r, h, hr => by simp [rename, rename_closed A r h hr]
  | .imm _ A, _, r, h, hr => by simp [rename, rename_closed A r h hr]
  | .mut _ A, _, r, h, hr => by simp [rename, rename_closed A r h hr]
  | .box _ A, _, r, h, hr => by simp [rename, rename_closed A r h hr]
  | .bang A, _, r, h, hr => by simp [rename, rename_closed A r h hr]
  | .fam A, _, r, h, hr => by simp [rename, rename_closed A r h hr]
  | .unk, _, _, _, _ => rfl
  | .int _, _, _, _, _ => rfl
  | .opq _, _, _, _, _ => rfl
  | .tvar n, _, _, h, hr => by simp [rename, hr n h]
  | .mu A, _, r, h, hr => by
      simp only [rename]
      rw [rename_closed A (upR r) h (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [upR, hr n (Nat.lt_of_succ_lt_succ hn)])]

theorem subst_closed : ∀ (A : VTy) {k : Nat} (σ : Nat → VTy), Cl k A →
    (∀ n, n < k → σ n = .tvar n) → subst σ A = A
  | .unit, _, _, _, _ => rfl
  | .tensor A B, _, σ, h, hσ => by simp [subst, subst_closed A σ h.1 hσ, subst_closed B σ h.2 hσ]
  | .zero, _, _, _, _ => rfl
  | .sum A B, _, σ, h, hσ => by simp [subst, subst_closed A σ h.1 hσ, subst_closed B σ h.2 hσ]
  | .thunk _, _, _, _, _ => rfl
  | .ref A, _, σ, h, hσ => by simp [subst, subst_closed A σ h hσ]
  | .imm _ A, _, σ, h, hσ => by simp [subst, subst_closed A σ h hσ]
  | .mut _ A, _, σ, h, hσ => by simp [subst, subst_closed A σ h hσ]
  | .box _ A, _, σ, h, hσ => by simp [subst, subst_closed A σ h hσ]
  | .bang A, _, σ, h, hσ => by simp [subst, subst_closed A σ h hσ]
  | .fam A, _, σ, h, hσ => by simp [subst, subst_closed A σ h hσ]
  | .unk, _, _, _, _ => rfl
  | .int _, _, _, _, _ => rfl
  | .opq _, _, _, _, _ => rfl
  | .tvar n, _, _, h, hσ => hσ n h
  | .mu A, _, σ, h, hσ => by
      simp only [subst]
      rw [subst_closed A (upS σ) h (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [upS, scons, hσ n (Nat.lt_of_succ_lt_succ hn), rename])]

/-- Substitutions agreeing below `k` agree on a type closed at `k`. -/
theorem subst_congr : ∀ (A : VTy) {k : Nat} {σ τ : Nat → VTy}, Cl k A →
    (∀ n, n < k → σ n = τ n) → subst σ A = subst τ A
  | .unit, _, _, _, _, _ => rfl
  | .tensor A B, _, _, _, h, hσ => by simp [subst, subst_congr A h.1 hσ, subst_congr B h.2 hσ]
  | .zero, _, _, _, _, _ => rfl
  | .sum A B, _, _, _, h, hσ => by simp [subst, subst_congr A h.1 hσ, subst_congr B h.2 hσ]
  | .thunk _, _, _, _, _, _ => rfl
  | .ref A, _, _, _, h, hσ => by simp [subst, subst_congr A h hσ]
  | .imm _ A, _, _, _, h, hσ => by simp [subst, subst_congr A h hσ]
  | .mut _ A, _, _, _, h, hσ => by simp [subst, subst_congr A h hσ]
  | .box _ A, _, _, _, h, hσ => by simp [subst, subst_congr A h hσ]
  | .bang A, _, _, _, h, hσ => by simp [subst, subst_congr A h hσ]
  | .fam A, _, _, _, h, hσ => by simp [subst, subst_congr A h hσ]
  | .unk, _, _, _, _, _ => rfl
  | .int _, _, _, _, _, _ => rfl
  | .opq _, _, _, _, _, _ => rfl
  | .tvar n, _, _, _, h, hσ => hσ n h
  | .mu A, _, σ, τ, h, hσ => by
      simp only [subst]
      rw [subst_congr A h (σ := upS σ) (τ := upS τ) (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [upS, scons, hσ n (Nat.lt_of_succ_lt_succ hn)])]

/-- A closed type is fixed by every substitution. -/
theorem subst_closed0 {A : VTy} (h : Cl 0 A) (σ : Nat → VTy) : subst σ A = A :=
  subst_closed A σ h (fun _ hn => absurd hn (Nat.not_lt_zero _))

theorem rename_closed0 {A : VTy} (h : Cl 0 A) (r : Nat → Nat) : rename r A = A :=
  rename_closed A r h (fun _ hn => absurd hn (Nat.not_lt_zero _))

/-- `T[S/X]` of a type closed at `1` by a closed `S` is closed. -/
theorem Cl_inst {S T : VTy} (hS : Cl 0 S) (hT : Cl 1 T) : Cl 0 (inst S T) :=
  Cl_substB T _ hT (fun n hn => by
    cases n with
    | zero => exact hS
    | succ n => exact absurd hn (by omega))

/-! ### Occurrence and positivity -/

/-- The variable `k` occurs free in `A`. -/
def Occ : Nat → VTy → Prop
  | _, .unit => False
  | k, .tensor A B => Occ k A ∨ Occ k B
  | _, .zero => False
  | k, .sum A B => Occ k A ∨ Occ k B
  | _, .thunk _ => False
  | k, .ref A => Occ k A
  | k, .imm _ A => Occ k A
  | k, .mut _ A => Occ k A
  | k, .box _ A => Occ k A
  | k, .bang A => Occ k A
  | k, .fam A => Occ k A
  | _, .unk => False
  | _, .int _ => False
  | _, .opq _ => False
  | k, .tvar n => n = k
  | k, .mu A => Occ (k + 1) A

/-- The variable `k` occurs in `A` only outside `Mut` payloads — `docs/scope-recursion.md` §2.2:
the `Mut` clause stores its predicate by an equation, so it is not monotone.  A `U C` is a
leaf, so a variable never occurs in a `⊸` domain.  `[spec §6]` -/
def NoMut : Nat → VTy → Prop
  | _, .unit => True
  | k, .tensor A B => NoMut k A ∧ NoMut k B
  | _, .zero => True
  | k, .sum A B => NoMut k A ∧ NoMut k B
  | _, .thunk _ => True
  | k, .ref A => NoMut k A
  | k, .imm _ A => NoMut k A
  | k, .mut _ A => ¬ Occ k A
  | k, .box _ A => NoMut k A
  | k, .bang A => NoMut k A
  | k, .fam A => NoMut k A
  | _, .unk => True
  | _, .int _ => True
  | _, .opq _ => True
  | _, .tvar _ => True
  | k, .mu A => NoMut (k + 1) A

theorem noMut_of_not_occ : ∀ (A : VTy) {k : Nat}, ¬ Occ k A → NoMut k A
  | .unit, _, _ => trivial
  | .tensor A B, _, h => ⟨noMut_of_not_occ A (fun h' => h (Or.inl h')),
      noMut_of_not_occ B (fun h' => h (Or.inr h'))⟩
  | .zero, _, _ => trivial
  | .sum A B, _, h => ⟨noMut_of_not_occ A (fun h' => h (Or.inl h')),
      noMut_of_not_occ B (fun h' => h (Or.inr h'))⟩
  | .thunk _, _, _ => trivial
  | .ref A, _, h => noMut_of_not_occ A h
  | .imm _ A, _, h => noMut_of_not_occ A h
  | .mut _ A, _, h => h
  | .box _ A, _, h => noMut_of_not_occ A h
  | .bang A, _, h => noMut_of_not_occ A h
  | .fam A, _, h => noMut_of_not_occ A h
  | .unk, _, _ => trivial
  | .int _, _, _ => trivial
  | .opq _, _, _ => trivial
  | .tvar _, _, _ => trivial
  | .mu A, _, h => noMut_of_not_occ A h

theorem not_occ_of_Cl : ∀ (A : VTy) {j k : Nat}, Cl j A → j ≤ k → ¬ Occ k A
  | .unit, _, _, _, _, h => h
  | .tensor A B, _, _, hc, hk, h => h.elim (not_occ_of_Cl A hc.1 hk) (not_occ_of_Cl B hc.2 hk)
  | .zero, _, _, _, _, h => h
  | .sum A B, _, _, hc, hk, h => h.elim (not_occ_of_Cl A hc.1 hk) (not_occ_of_Cl B hc.2 hk)
  | .thunk _, _, _, _, _, h => h
  | .ref A, _, _, hc, hk, h => not_occ_of_Cl A hc hk h
  | .imm _ A, _, _, hc, hk, h => not_occ_of_Cl A hc hk h
  | .mut _ A, _, _, hc, hk, h => not_occ_of_Cl A hc hk h
  | .box _ A, _, _, hc, hk, h => not_occ_of_Cl A hc hk h
  | .bang A, _, _, hc, hk, h => not_occ_of_Cl A hc hk h
  | .fam A, _, _, hc, hk, h => not_occ_of_Cl A hc hk h
  | .unk, _, _, _, _, h => h
  | .int _, _, _, _, _, h => h
  | .opq _, _, _, _, _, h => h
  | .tvar n, _, _, hc, hk, h => by simp only [Cl] at hc; simp only [Occ] at h; omega
  | .mu A, _, _, hc, hk, h => not_occ_of_Cl A hc (Nat.succ_le_succ hk) h

theorem occ_rename : ∀ (A : VTy) {k : Nat} (r : Nat → Nat), Occ k (rename r A) → ∃ n, r n = k ∧ Occ n A
  | .unit, _, _, h => h.elim
  | .tensor A B, _, r, h => h.elim
      (fun h => let ⟨n, hn, h⟩ := occ_rename A r h; ⟨n, hn, Or.inl h⟩)
      (fun h => let ⟨n, hn, h⟩ := occ_rename B r h; ⟨n, hn, Or.inr h⟩)
  | .zero, _, _, h => h.elim
  | .sum A B, _, r, h => h.elim
      (fun h => let ⟨n, hn, h⟩ := occ_rename A r h; ⟨n, hn, Or.inl h⟩)
      (fun h => let ⟨n, hn, h⟩ := occ_rename B r h; ⟨n, hn, Or.inr h⟩)
  | .thunk _, _, _, h => h.elim
  | .ref A, _, r, h => occ_rename A r h
  | .imm _ A, _, r, h => occ_rename A r h
  | .mut _ A, _, r, h => occ_rename A r h
  | .box _ A, _, r, h => occ_rename A r h
  | .bang A, _, r, h => occ_rename A r h
  | .fam A, _, r, h => occ_rename A r h
  | .unk, _, _, h => h.elim
  | .int _, _, _, h => h.elim
  | .opq _, _, _, h => h.elim
  | .tvar n, _, _, h => ⟨n, h, rfl⟩
  | .mu A, k, r, h => by
      obtain ⟨n, hn, h⟩ := occ_rename A (upR r) h
      cases n with
      | zero => exact absurd hn (by simp [upR])
      | succ n =>
          simp only [upR, Nat.add_right_cancel_iff] at hn
          exact ⟨n, hn, h⟩

theorem occ_subst : ∀ (A : VTy) {k : Nat} (τ : Nat → VTy), Occ k (subst τ A) →
    ∃ n, Occ n A ∧ Occ k (τ n)
  | .unit, _, _, h => h.elim
  | .tensor A B, _, τ, h => h.elim
      (fun h => let ⟨n, hn, h⟩ := occ_subst A τ h; ⟨n, Or.inl hn, h⟩)
      (fun h => let ⟨n, hn, h⟩ := occ_subst B τ h; ⟨n, Or.inr hn, h⟩)
  | .zero, _, _, h => h.elim
  | .sum A B, _, τ, h => h.elim
      (fun h => let ⟨n, hn, h⟩ := occ_subst A τ h; ⟨n, Or.inl hn, h⟩)
      (fun h => let ⟨n, hn, h⟩ := occ_subst B τ h; ⟨n, Or.inr hn, h⟩)
  | .thunk _, _, _, h => h.elim
  | .ref A, _, τ, h => occ_subst A τ h
  | .imm _ A, _, τ, h => occ_subst A τ h
  | .mut _ A, _, τ, h => occ_subst A τ h
  | .box _ A, _, τ, h => occ_subst A τ h
  | .bang A, _, τ, h => occ_subst A τ h
  | .fam A, _, τ, h => occ_subst A τ h
  | .unk, _, _, h => h.elim
  | .int _, _, _, h => h.elim
  | .opq _, _, _, h => h.elim
  | .tvar n, _, _, h => ⟨n, rfl, h⟩
  | .mu A, k, τ, h => by
      obtain ⟨n, hn, h⟩ := occ_subst A (upS τ) h
      cases n with
      | zero => exact absurd h (by simp [upS, scons, Occ])
      | succ n =>
          obtain ⟨j, hj, h₂⟩ := occ_rename (τ n) Nat.succ h
          have hj' : j = k := Nat.succ.inj hj
          subst hj'
          exact ⟨n, hn, h₂⟩

theorem subst_congr_occ : ∀ (A : VTy) {σ τ : Nat → VTy}, (∀ n, Occ n A → σ n = τ n) →
    subst σ A = subst τ A
  | .unit, _, _, _ => rfl
  | .tensor A B, _, _, h => by
      simp [subst, subst_congr_occ A (fun n hn => h n (Or.inl hn)),
        subst_congr_occ B (fun n hn => h n (Or.inr hn))]
  | .zero, _, _, _ => rfl
  | .sum A B, _, _, h => by
      simp [subst, subst_congr_occ A (fun n hn => h n (Or.inl hn)),
        subst_congr_occ B (fun n hn => h n (Or.inr hn))]
  | .thunk _, _, _, _ => rfl
  | .ref A, _, _, h => by simp [subst, subst_congr_occ A h]
  | .imm _ A, _, _, h => by simp [subst, subst_congr_occ A h]
  | .mut _ A, _, _, h => by simp [subst, subst_congr_occ A h]
  | .box _ A, _, _, h => by simp [subst, subst_congr_occ A h]
  | .bang A, _, _, h => by simp [subst, subst_congr_occ A h]
  | .fam A, _, _, h => by simp [subst, subst_congr_occ A h]
  | .unk, _, _, _ => rfl
  | .int _, _, _, _ => rfl
  | .opq _, _, _, _ => rfl
  | .tvar n, _, _, h => h n rfl
  | .mu A, σ, τ, h => by
      simp only [subst]
      rw [subst_congr_occ A (σ := upS σ) (τ := upS τ) (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp only [upS, scons]; rw [h n hn])]

theorem occ_rename_of : ∀ (A : VTy) {j : Nat} (r : Nat → Nat), Occ j A → Occ (r j) (rename r A)
  | .unit, _, _, h => h
  | .tensor A B, _, r, h => h.elim (fun h => Or.inl (occ_rename_of A r h))
      (fun h => Or.inr (occ_rename_of B r h))
  | .zero, _, _, h => h
  | .sum A B, _, r, h => h.elim (fun h => Or.inl (occ_rename_of A r h))
      (fun h => Or.inr (occ_rename_of B r h))
  | .thunk _, _, _, h => h
  | .ref A, _, r, h => occ_rename_of A r h
  | .imm _ A, _, r, h => occ_rename_of A r h
  | .mut _ A, _, r, h => occ_rename_of A r h
  | .box _ A, _, r, h => occ_rename_of A r h
  | .bang A, _, r, h => occ_rename_of A r h
  | .fam A, _, r, h => occ_rename_of A r h
  | .unk, _, _, h => h
  | .int _, _, _, h => h
  | .opq _, _, _, h => h
  | .tvar n, _, r, h => by simp only [Occ] at h; subst h; rfl
  | .mu A, j, r, h => occ_rename_of A (upR r) (j := j + 1) h

theorem occ_subst_of : ∀ (A : VTy) {n k : Nat} (τ : Nat → VTy), Occ n A → Occ k (τ n) →
    Occ k (subst τ A)
  | .unit, _, _, _, h, _ => h.elim
  | .tensor A B, _, _, τ, h, hk => h.elim (fun h => Or.inl (occ_subst_of A τ h hk))
      (fun h => Or.inr (occ_subst_of B τ h hk))
  | .zero, _, _, _, h, _ => h.elim
  | .sum A B, _, _, τ, h, hk => h.elim (fun h => Or.inl (occ_subst_of A τ h hk))
      (fun h => Or.inr (occ_subst_of B τ h hk))
  | .thunk _, _, _, _, h, _ => h.elim
  | .ref A, _, _, τ, h, hk => occ_subst_of A τ h hk
  | .imm _ A, _, _, τ, h, hk => occ_subst_of A τ h hk
  | .mut _ A, _, _, τ, h, hk => occ_subst_of A τ h hk
  | .box _ A, _, _, τ, h, hk => occ_subst_of A τ h hk
  | .bang A, _, _, τ, h, hk => occ_subst_of A τ h hk
  | .fam A, _, _, τ, h, hk => occ_subst_of A τ h hk
  | .unk, _, _, _, h, _ => h.elim
  | .int _, _, _, _, h, _ => h.elim
  | .opq _, _, _, _, h, _ => h.elim
  | .tvar m, _, _, τ, h, hk => by simp only [Occ] at h; subst h; exact hk
  | .mu A, n, k, τ, h, hk => occ_subst_of A (upS τ) (n := n + 1) (k := k + 1) h
      (occ_rename_of (τ n) Nat.succ hk)

theorem noMut_of_subst : ∀ (A : VTy) {k : Nat} (τ : Nat → VTy), NoMut k (subst τ A) →
    τ k = .tvar k → NoMut k A
  | .unit, _, _, _, _ => trivial
  | .tensor A B, _, τ, h, hk => ⟨noMut_of_subst A τ h.1 hk, noMut_of_subst B τ h.2 hk⟩
  | .zero, _, _, _, _ => trivial
  | .sum A B, _, τ, h, hk => ⟨noMut_of_subst A τ h.1 hk, noMut_of_subst B τ h.2 hk⟩
  | .thunk _, _, _, _, _ => trivial
  | .ref A, _, τ, h, hk => noMut_of_subst A τ h hk
  | .imm _ A, _, τ, h, hk => noMut_of_subst A τ h hk
  | .mut _ A, k, τ, h, hk => fun ho => h (occ_subst_of A τ ho (by rw [hk]; rfl))
  | .box _ A, _, τ, h, hk => noMut_of_subst A τ h hk
  | .bang A, _, τ, h, hk => noMut_of_subst A τ h hk
  | .fam A, _, τ, h, hk => noMut_of_subst A τ h hk
  | .unk, _, _, _, _ => trivial
  | .int _, _, _, _, _ => trivial
  | .opq _, _, _, _, _ => trivial
  | .tvar _, _, _, _, _ => trivial
  | .mu A, k, τ, h, hk => noMut_of_subst A (upS τ) h (by simp [upS, scons, hk, rename])

theorem noMut_subst : ∀ (A : VTy) {k : Nat} (τ : Nat → VTy), NoMut k A → τ k = .tvar k →
    (∀ n, n ≠ k → ¬ Occ k (τ n)) → NoMut k (subst τ A)
  | .unit, _, _, _, _, _ => trivial
  | .tensor A B, _, τ, h, hk, hτ => ⟨noMut_subst A τ h.1 hk hτ, noMut_subst B τ h.2 hk hτ⟩
  | .zero, _, _, _, _, _ => trivial
  | .sum A B, _, τ, h, hk, hτ => ⟨noMut_subst A τ h.1 hk hτ, noMut_subst B τ h.2 hk hτ⟩
  | .thunk _, _, _, _, _, _ => trivial
  | .ref A, _, τ, h, hk, hτ => noMut_subst A τ h hk hτ
  | .imm _ A, _, τ, h, hk, hτ => noMut_subst A τ h hk hτ
  | .mut _ A, k, τ, h, _, hτ => fun ho => by
      obtain ⟨n, hn, ho⟩ := occ_subst A τ ho
      by_cases e : n = k
      · subst e; exact h hn
      · exact hτ n e ho
  | .box _ A, _, τ, h, hk, hτ => noMut_subst A τ h hk hτ
  | .bang A, _, τ, h, hk, hτ => noMut_subst A τ h hk hτ
  | .fam A, _, τ, h, hk, hτ => noMut_subst A τ h hk hτ
  | .unk, _, _, _, _, _ => trivial
  | .int _, _, _, _, _, _ => trivial
  | .opq _, _, _, _, _, _ => trivial
  | .tvar n, k, τ, _, hk, hτ => by
      show NoMut k (τ n)
      by_cases e : n = k
      · subst e; rw [hk]; trivial
      · exact noMut_of_not_occ _ (hτ n e)
  | .mu A, k, τ, h, hk, hτ => noMut_subst A (upS τ) h (by simp [upS, scons, hk, rename])
      (fun n hn => by
        cases n with
        | zero => simp [upS, scons, Occ]
        | succ n =>
            intro ho
            obtain ⟨j, hj, ho₂⟩ := occ_rename (τ n) Nat.succ ho
            have hj' : j = k := Nat.succ.inj hj
            subst hj'
            exact hτ n (fun e => hn (by rw [e])) ho₂)

theorem rename_eq_subst : ∀ (A : VTy) (r : Nat → Nat), rename r A = subst (fun n => .tvar (r n)) A
  | .unit, _ => rfl
  | .tensor A B, r => by simp [rename, subst, rename_eq_subst A, rename_eq_subst B]
  | .zero, _ => rfl
  | .sum A B, r => by simp [rename, subst, rename_eq_subst A, rename_eq_subst B]
  | .thunk _, _ => rfl
  | .ref A, r => by simp [rename, subst, rename_eq_subst A]
  | .imm _ A, r => by simp [rename, subst, rename_eq_subst A]
  | .mut _ A, r => by simp [rename, subst, rename_eq_subst A]
  | .box _ A, r => by simp [rename, subst, rename_eq_subst A]
  | .bang A, r => by simp [rename, subst, rename_eq_subst A]
  | .fam A, r => by simp [rename, subst, rename_eq_subst A]
  | .unk, _ => rfl
  | .int _, _ => rfl
  | .opq _, _ => rfl
  | .tvar _, _ => rfl
  | .mu A, r => by
      simp only [rename, subst, rename_eq_subst A]
      congr 2
      funext n; cases n <;> rfl

theorem noMut_rename_upR_iff (A : VTy) (r : Nat → Nat) : NoMut 0 (rename (upR r) A) ↔ NoMut 0 A := by
  rw [rename_eq_subst]
  constructor
  · intro h; exact noMut_of_subst A _ h rfl
  · intro h
    exact noMut_subst A _ h rfl (fun n hn => by
      cases n with
      | zero => exact absurd rfl hn
      | succ n => simp [upR, Occ])

theorem noMut_upS_iff (A : VTy) (σ : Nat → VTy) : NoMut 0 (subst (upS σ) A) ↔ NoMut 0 A := by
  constructor
  · intro h
    exact noMut_of_subst A (upS σ) h rfl
  · intro h
    exact noMut_subst A (upS σ) h rfl (fun n hn => by
      cases n with
      | zero => exact absurd rfl hn
      | succ n =>
          intro ho
          obtain ⟨j, hj, -⟩ := occ_rename (σ n) Nat.succ ho
          exact Nat.succ_ne_zero j hj)

/-! ### `Imm̲` with a payload substitution -/

/-- `Imm̲ 'b` at `pay`: a head-position variable is kept; a payload kept by the `Ref`, `Imm`,
`Mut` or `!` clause has every variable replaced by the closed type it stands for (`pay`). At
`μX. A` the new variable stands for `μX. A` itself. -/
def immG (b : Lifetime.Life) (pay : Nat → VTy) : VTy → VTy
  | .unit => .unit
  | .tensor A B => .tensor (immG b pay A) (immG b pay B)
  | .zero => .zero
  | .sum A B => .sum (immG b pay A) (immG b pay B)
  | .thunk _ => .unk
  | .ref A => .imm b (subst pay A)
  | .imm a A => .imm a (subst pay A)
  | .mut _ A => .imm b (subst pay A)
  | .box _ A => immG b pay A
  | .bang A => .bang (subst pay A)
  | .fam A => .fam (immG b pay A)
  | .unk => .unk
  | .int w => .int w
  | .opq _ => .unk
  | .tvar n => .tvar n
  | .mu A => .mu (immG b (scons (subst pay (.mu A)) pay) A)

/-- The default payload substitution, for closed types (never consulted). -/
abbrev dflt : Nat → VTy := fun _ => .unit

/-- `Imm̲ 'b A` on closed types. -/
def immReb (b : Lifetime.Life) (A : VTy) : VTy := immG b dflt A

/-- `Imm̲ᵡ 'b T` for `μX. T`: head `X` stays the variable, payload `X` becomes `μX. T`. -/
def immX (b : Lifetime.Life) (T : VTy) : VTy := immG b (scons (.mu T) dflt) T

section
variable (b : Lifetime.Life)

theorem scons_closed {x : VTy} {f : Nat → VTy} (hx : Cl 0 x) (hf : ∀ n, Cl 0 (f n)) :
    ∀ n, Cl 0 (scons x f n)
  | 0 => hx
  | n + 1 => hf n

/-- `Imm̲` commutes with renaming. -/
theorem immG_rename : ∀ (A : VTy) (pay : Nat → VTy) (r : Nat → Nat), (∀ n, Cl 0 (pay n)) →
    immG b pay (rename r A) = rename r (immG b (pay ∘ r) A)
  | .unit, _, _, _ => rfl
  | .tensor A B, pay, r, h => by
      simp [immG, rename, immG_rename A pay r h, immG_rename B pay r h]
  | .zero, _, _, _ => rfl
  | .sum A B, pay, r, h => by
      simp [immG, rename, immG_rename A pay r h, immG_rename B pay r h]
  | .thunk _, _, _, _ => rfl
  | .ref A, pay, r, h => by
      simp only [immG, rename, subst_rename]
      rw [rename_closed0 (Cl_subst A (pay ∘ r) (fun n => h (r n)))]
  | .imm _ A, pay, r, h => by
      simp only [immG, rename, subst_rename]
      rw [rename_closed0 (Cl_subst A (pay ∘ r) (fun n => h (r n)))]
  | .mut _ A, pay, r, h => by
      simp only [immG, rename, subst_rename]
      rw [rename_closed0 (Cl_subst A (pay ∘ r) (fun n => h (r n)))]
  | .box _ A, pay, r, h => by simp [immG, rename, immG_rename A pay r h]
  | .bang A, pay, r, h => by
      simp only [immG, rename, subst_rename]
      rw [rename_closed0 (Cl_subst A (pay ∘ r) (fun n => h (r n)))]
  | .fam A, pay, r, h => by simp [immG, rename, immG_rename A pay r h]
  | .unk, _, _, _ => rfl
  | .int _, _, _, _ => rfl
  | .opq _, _, _, _ => rfl
  | .tvar _, _, _, _ => rfl
  | .mu A, pay, r, h => by
      have hc : Cl 0 (subst pay (.mu (rename (upR r) A))) := Cl_subst _ pay h
      simp only [immG, rename]
      rw [immG_rename A _ (upR r) (scons_closed hc h)]
      congr 3
      funext n
      cases n with
      | zero =>
          show subst pay (.mu (rename (upR r) A)) = subst (pay ∘ r) (.mu A)
          rw [← subst_rename]; rfl
      | succ n => rfl

/-- **`Imm̲` commutes with substitution**, for a closed payload substitution. -/
theorem immG_subst : ∀ (A : VTy) (pay σ : Nat → VTy), (∀ n, Cl 0 (pay n)) →
    immG b pay (subst σ A)
      = subst (fun n => immG b pay (σ n)) (immG b (fun n => subst pay (σ n)) A)
  | .unit, _, _, _ => rfl
  | .tensor A B, pay, σ, h => by
      simp [immG, subst, immG_subst A pay σ h, immG_subst B pay σ h]
  | .zero, _, _, _ => rfl
  | .sum A B, pay, σ, h => by
      simp [immG, subst, immG_subst A pay σ h, immG_subst B pay σ h]
  | .thunk _, _, _, _ => rfl
  | .ref A, pay, σ, h => by
      simp only [immG, subst]
      rw [subst_closed0 (Cl_subst A (fun n => subst pay (σ n)) (fun n => Cl_subst (σ n) pay h)),
        subst_subst]
  | .imm _ A, pay, σ, h => by
      simp only [immG, subst]
      rw [subst_closed0 (Cl_subst A (fun n => subst pay (σ n)) (fun n => Cl_subst (σ n) pay h)),
        subst_subst]
  | .mut _ A, pay, σ, h => by
      simp only [immG, subst]
      rw [subst_closed0 (Cl_subst A (fun n => subst pay (σ n)) (fun n => Cl_subst (σ n) pay h)),
        subst_subst]
  | .box _ A, pay, σ, h => by simp [immG, subst, immG_subst A pay σ h]
  | .bang A, pay, σ, h => by
      simp only [immG, subst]
      rw [subst_closed0 (Cl_subst A (fun n => subst pay (σ n)) (fun n => Cl_subst (σ n) pay h)),
        subst_subst]
  | .fam A, pay, σ, h => by simp [immG, subst, immG_subst A pay σ h]
  | .unk, _, _, _ => rfl
  | .int _, _, _, _ => rfl
  | .opq _, _, _, _ => rfl
  | .tvar _, _, _, _ => rfl
  | .mu A, pay, σ, h => by
      have hc : Cl 0 (subst pay (.mu (subst (upS σ) A))) := Cl_subst _ pay h
      have h₁ := scons_closed hc h
      show VTy.mu (immG b (scons (subst pay (.mu (subst (upS σ) A))) pay) (subst (upS σ) A))
        = VTy.mu (subst (upS (fun n => immG b pay (σ n)))
            (immG b (scons (subst (fun n => subst pay (σ n)) (.mu A))
              (fun n => subst pay (σ n))) A))
      rw [immG_subst A _ (upS σ) h₁]
      have e₁ : (fun n => subst (scons (subst pay (.mu (subst (upS σ) A))) pay) (upS σ n))
          = scons (subst (fun n => subst pay (σ n)) (.mu A)) (fun n => subst pay (σ n)) := by
        funext n
        cases n with
        | zero =>
            show subst pay (.mu (subst (upS σ) A)) = _
            rw [show VTy.mu (subst (upS σ) A) = subst σ (.mu A) from rfl, subst_subst]; rfl
        | succ n =>
            show subst _ (rename Nat.succ (σ n)) = subst pay (σ n)
            rw [subst_rename]; rfl
      have e₂ : (fun n => immG b (scons (subst pay (.mu (subst (upS σ) A))) pay) (upS σ n))
          = upS (fun n => immG b pay (σ n)) := by
        funext n
        cases n with
        | zero => rfl
        | succ n =>
            show immG b _ (rename Nat.succ (σ n)) = rename Nat.succ (immG b pay (σ n))
            rw [immG_rename b (σ n) _ Nat.succ h₁]; rfl
      rw [e₁, e₂]

/-- Payload substitutions agreeing below `k` agree on a type closed at `k`. -/
theorem immG_congr : ∀ (A : VTy) {k : Nat} {pay pay' : Nat → VTy}, Cl k A →
    (∀ n, n < k → pay n = pay' n) → immG b pay A = immG b pay' A
  | .unit, _, _, _, _, _ => rfl
  | .tensor A B, _, _, _, h, hp => by simp [immG, immG_congr A h.1 hp, immG_congr B h.2 hp]
  | .zero, _, _, _, _, _ => rfl
  | .sum A B, _, _, _, h, hp => by simp [immG, immG_congr A h.1 hp, immG_congr B h.2 hp]
  | .thunk _, _, _, _, _, _ => rfl
  | .ref A, _, _, _, h, hp => by simp [immG, subst_congr A h hp]
  | .imm _ A, _, _, _, h, hp => by simp [immG, subst_congr A h hp]
  | .mut _ A, _, _, _, h, hp => by simp [immG, subst_congr A h hp]
  | .box _ A, _, _, _, h, hp => by simp [immG, immG_congr A h hp]
  | .bang A, _, _, _, h, hp => by simp [immG, subst_congr A h hp]
  | .fam A, _, _, _, h, hp => by simp [immG, immG_congr A h hp]
  | .unk, _, _, _, _, _ => rfl
  | .int _, _, _, _, _, _ => rfl
  | .opq _, _, _, _, _, _ => rfl
  | .tvar _, _, _, _, _, _ => rfl
  | .mu A, k, pay, pay', h, hp => by
      simp only [immG]
      rw [immG_congr A h (pay' := scons (subst pay' (.mu A)) pay') (fun n hn => by
        cases n with
        | zero => exact subst_congr (.mu A) (k := k) h hp
        | succ n => exact hp n (Nat.lt_of_succ_lt_succ hn))]

theorem Cl_immG : ∀ (A : VTy) {k : Nat} (pay : Nat → VTy), (∀ n, Cl 0 (pay n)) → Cl k A →
    Cl k (immG b pay A)
  | .unit, _, _, _, _ => trivial
  | .tensor A B, _, pay, hp, h => ⟨Cl_immG A pay hp h.1, Cl_immG B pay hp h.2⟩
  | .zero, _, _, _, _ => trivial
  | .sum A B, _, pay, hp, h => ⟨Cl_immG A pay hp h.1, Cl_immG B pay hp h.2⟩
  | .thunk _, _, _, _, _ => trivial
  | .ref A, _, pay, hp, _ => Cl_mono _ (Cl_subst A pay hp) (Nat.zero_le _)
  | .imm _ A, _, pay, hp, _ => Cl_mono _ (Cl_subst A pay hp) (Nat.zero_le _)
  | .mut _ A, _, pay, hp, _ => Cl_mono _ (Cl_subst A pay hp) (Nat.zero_le _)
  | .box _ A, _, pay, hp, h => Cl_immG A pay hp h
  | .bang A, _, pay, hp, _ => Cl_mono _ (Cl_subst A pay hp) (Nat.zero_le _)
  | .fam A, _, pay, hp, h => Cl_immG A pay hp h
  | .unk, _, _, _, _ => trivial
  | .int _, _, _, _, _ => trivial
  | .opq _, _, _, _, _ => trivial
  | .tvar _, _, _, _, h => h
  | .mu A, _, pay, hp, h =>
      Cl_immG A _ (scons_closed (Cl_subst (.mu A) pay hp) hp) h

/-- The output of `Imm̲` holds no variable under a `Mut`: its payloads are closed. -/
theorem noMut_immG : ∀ (A : VTy) {k : Nat} (pay : Nat → VTy), (∀ n, Cl 0 (pay n)) →
    NoMut k (immG b pay A)
  | .unit, _, _, _ => trivial
  | .tensor A B, _, pay, hp => ⟨noMut_immG A pay hp, noMut_immG B pay hp⟩
  | .zero, _, _, _ => trivial
  | .sum A B, _, pay, hp => ⟨noMut_immG A pay hp, noMut_immG B pay hp⟩
  | .thunk _, _, _, _ => trivial
  | .ref A, _, pay, hp => noMut_of_not_occ _ (not_occ_of_Cl _ (Cl_subst A pay hp) (Nat.zero_le _))
  | .imm _ A, _, pay, hp => noMut_of_not_occ _ (not_occ_of_Cl _ (Cl_subst A pay hp) (Nat.zero_le _))
  | .mut _ A, _, pay, hp => noMut_of_not_occ _ (not_occ_of_Cl _ (Cl_subst A pay hp) (Nat.zero_le _))
  | .box _ A, _, pay, hp => noMut_immG A pay hp
  | .bang A, _, pay, hp => noMut_of_not_occ _ (not_occ_of_Cl _ (Cl_subst A pay hp) (Nat.zero_le _))
  | .fam A, _, pay, hp => noMut_immG A pay hp
  | .unk, _, _, _ => trivial
  | .int _, _, _, _ => trivial
  | .opq _, _, _, _ => trivial
  | .tvar _, _, _, _ => trivial
  | .mu A, _, pay, hp => noMut_immG A _ (scons_closed (Cl_subst (.mu A) pay hp) hp)

/-- **The unrolling law at `μ`.** `Imm̲ 'b (T[μX.T/X]) = (Imm̲ᵡ 'b T)[Imm̲ 'b (μX.T)/Y]`. -/
theorem immReb_unroll {T : VTy} (hT : Cl 1 T) :
    immReb b (inst (.mu T) T) = inst (immReb b (.mu T)) (immX b T) := by
  have hdf : ∀ n, Cl 0 (dflt n) := fun _ => trivial
  have hmu : Cl 0 (VTy.mu T) := hT
  rw [immReb, inst, immG_subst b T dflt _ hdf, inst, immX]
  have e₁ : (fun n => subst dflt (scons (.mu T) .tvar n)) = scons (.mu T) dflt := by
    funext n; cases n with
    | zero => exact subst_closed0 hmu dflt
    | succ n => rfl
  have e₂ : (fun n => immG b dflt (scons (.mu T) .tvar n)) = scons (immReb b (.mu T)) .tvar := by
    funext n; cases n <;> rfl
  rw [e₁, e₂]

/-- `Imm̲ 'b (μX.T) = μY. Imm̲ᵡ 'b T` on a closed `μ`. -/
theorem immReb_mu {T : VTy} (hT : Cl 1 T) : immReb b (.mu T) = .mu (immX b T) := by
  simp only [immReb, immG, immX, subst_closed0 (show Cl 0 (VTy.mu T) from hT)]

end

end VTy

/-! ### `νX. C`: observation trees, positivity, unrolling  `[spec §7]`

In `νX. C` the value type `U X` is the type variable `0` of `C`'s value types.  `C` is a
`&`-tree of observations `F A` (`NuLeaf`), headed by `&` (`NuOk`), with `X` occurring in each
`A` only under `⊗`, `⊕` and `[@a]` (`VTy.Poly`): there the relation is monotone in `X` and coiteration
maps a state to the rest. -/

/-- `X` occurs in `A` only under `⊗`, `⊕` and `[@a]`: a variable, or `⊗`/`⊕`/`[@a]` of such
types, or a type in which `X` does not occur.  `[spec §22]`: the rest of a closure that
outlives `@a` is `[@a] U X`. -/
def VTy.Poly : VTy → Prop
  | .tensor A B => A.Poly ∧ B.Poly
  | .sum A B => A.Poly ∧ B.Poly
  | .box _ A => A.Poly
  | .tvar _ => True
  | A => ¬ A.Occ 0

theorem VTy.noMut_of_poly : ∀ {A : VTy}, A.Poly → A.NoMut 0
  | .tensor _ _, h => ⟨noMut_of_poly h.1, noMut_of_poly h.2⟩
  | .sum _ _, h => ⟨noMut_of_poly h.1, noMut_of_poly h.2⟩
  | .box _ A, h => noMut_of_poly (A := A) h
  | .tvar _, _ => trivial
  | .unit, _ | .zero, _ | .thunk _, _ | .unk, _ | .int _, _ | .opq _, _ => trivial
  | .ref _, h | .imm _ _, h | .mut _ _, h | .bang _, h | .fam _, h | .mu _, h =>
      VTy.noMut_of_not_occ _ h

namespace CTy

/-- `C[S/X]` at the observations of a `&`-tree: `F A[S/X]` at each `F A`, and `F_Σ A[S/X]` at
each `F_Σ A`, whose operation types are closed.  `[spec §7, §19]` -/
def instT (S : VTy) : CTy → CTy
  | .ret A => .ret (VTy.inst S A)
  | .amp C D => .amp (instT S C) (instT S D)
  | .eff n i q A B fin rc C => .eff n i q A B fin rc (instT S C)
  | .arr A C => .arr A (instT S C)
  | C => C

/-- An effectful observation `F_Σ A`: a row's layers over `F A`, the operation types closed and
`A` polynomial in `X`.  `[spec §19]` -/
def EffLeaf : CTy → Prop
  | .ret A => A.Poly
  | .eff _ _ _ A B _ _ C => A.Cl 0 ∧ B.Cl 0 ∧ EffLeaf C
  | _ => False

/-- A `&`-tree of observations `F A` and `F_Σ A`, each `A` polynomial in `X`, and observations
with an argument `A ⊸ D` over such a tree, the argument type closed (the closure's
`call`).  `[spec §7, §19, §22]` -/
def NuLeaf : CTy → Prop
  | .ret A => A.Poly
  | .amp C D => NuLeaf C ∧ NuLeaf D
  | .eff n i q A B fin rc C => EffLeaf (.eff n i q A B fin rc C)
  | .arr A D => A.Cl 0 ∧ NuLeaf D
  | _ => False

/-- **Positivity** of `νX. C`: `C` is a `&` of two observation trees. -/
def NuOk : CTy → Prop
  | .amp C D => NuLeaf C ∧ NuLeaf D
  | _ => False

/-- The unrolling `C[U(νX. C)/X]`. -/
abbrev unroll (C : CTy) : CTy := instT (.thunk (.nu C)) C

/-- The body of `Loop A B = νX. F(A ⊕ U X) & F B`.  `[spec §7, §11]` -/
abbrev loopBody (A B : VTy) : CTy :=
  .amp (.ret (.sum (A.rename Nat.succ) (.tvar 0))) (.ret (B.rename Nat.succ))

/-- The body of `D A = Loop A 1`. -/
abbrev delayBody (A : VTy) : CTy := loopBody A .unit

/-- The body of `Loop_Σ A B = νX. F_Σ(A ⊕ U X) & F_Σ B`: a loop whose observations perform the
operations of `Σ`.  `[spec §19]` -/
abbrev loopEffBody (S : List OpSig) (A B : VTy) : CTy :=
  .amp (CTy.effOf S (.sum (A.rename Nat.succ) (.tvar 0))) (CTy.effOf S (B.rename Nat.succ))

/-- `Loop_Σ A B`.  `[spec §19]` -/
abbrev loopEff (S : List OpSig) (A B : VTy) : CTy := .nu (loopEffBody S A B)

/-- The body of `Stream A = νX. F(A ⊗ U X) & F 1`. -/
abbrev streamBody (A : VTy) : CTy :=
  .amp (.ret (.tensor (A.rename Nat.succ) (.tvar 0))) (.ret .unit)

/-- The body of `Iter A R R' = νX. F((A ⊗ U X) ⊕ R) & F R'`. -/
abbrev iterBody (A R R' : VTy) : CTy :=
  .amp (.ret (.sum (.tensor (A.rename Nat.succ) (.tvar 0)) (R.rename Nat.succ)))
    (.ret (R'.rename Nat.succ))

/-- `Loop A B = νX. F(A ⊕ U X) & F B`: a loop. `next` finishes with `A` or goes on; `close`
ends it early with the residual `B`.  `[spec §7, §11]` -/
abbrev loop (A B : VTy) : CTy := .nu (loopBody A B)

/-- `D A = Loop A 1`: the delay type. -/
abbrev delay (A : VTy) : CTy := .nu (delayBody A)

/-- `Stream A = νX. F(A ⊗ U X) & F 1`: the stream type. -/
abbrev stream (A : VTy) : CTy := .nu (streamBody A)

/-- `Iter A R R' = νX. F((A ⊗ U X) ⊕ R) & F R'`: a finite iterator. `next` yields an element and
the rest, or finishes with `R`; `close` returns the residual `R'`. -/
abbrev iter (A R R' : VTy) : CTy := .nu (iterBody A R R')

end CTy

/-- `A↑[S/X] = A`. -/
theorem VTy.inst_rename_succ (S A : VTy) : VTy.inst S (A.rename Nat.succ) = A := by
  rw [VTy.inst, VTy.subst_rename]
  exact VTy.subst_id A

theorem VTy.poly_of_not_occ : ∀ {A : VTy}, ¬ A.Occ 0 → A.Poly
  | .tensor _ _, h => ⟨poly_of_not_occ (fun h' => h (Or.inl h')),
      poly_of_not_occ (fun h' => h (Or.inr h'))⟩
  | .sum _ _, h => ⟨poly_of_not_occ (fun h' => h (Or.inl h')),
      poly_of_not_occ (fun h' => h (Or.inr h'))⟩
  | .box _ A, h => poly_of_not_occ (A := A) h
  | .tvar _, _ => trivial
  | .unit, h | .zero, h | .thunk _, h | .unk, h | .int _, h | .opq _, h => h
  | .ref _, h | .imm _ _, h | .mut _ _, h | .bang _, h | .fam _, h | .mu _, h => h

theorem VTy.not_occ_rename_succ (A : VTy) : ¬ (A.rename Nat.succ).Occ 0 := fun h => by
  obtain ⟨n, hn, -⟩ := VTy.occ_rename A Nat.succ h
  exact Nat.succ_ne_zero n hn

namespace CTy

theorem inst_sum_var (S A : VTy) :
    VTy.inst S (.sum (A.rename Nat.succ) (.tvar 0)) = .sum A S := by
  simp only [VTy.inst, VTy.subst, VTy.scons]
  rw [← VTy.inst, VTy.inst_rename_succ]

theorem loopBody_instT (A B S : VTy) :
    (loopBody A B).instT S = .amp (.ret (.sum A S)) (.ret B) := by
  simp only [instT, inst_sum_var, VTy.inst_rename_succ]

theorem delayBody_instT (A S : VTy) :
    (delayBody A).instT S = .amp (.ret (.sum A S)) (.ret .unit) := loopBody_instT A .unit S

theorem streamBody_instT (A S : VTy) :
    (streamBody A).instT S = .amp (.ret (.tensor A S)) (.ret .unit) := by
  simp only [instT, VTy.inst, VTy.subst, VTy.scons]
  rw [← VTy.inst, VTy.inst_rename_succ]

theorem iterBody_instT (A R R' S : VTy) :
    (iterBody A R R').instT S = .amp (.ret (.sum (.tensor A S) R)) (.ret R') := by
  simp only [instT, VTy.inst, VTy.subst, VTy.scons]
  rw [← VTy.inst, ← VTy.inst, ← VTy.inst, VTy.inst_rename_succ, VTy.inst_rename_succ,
    VTy.inst_rename_succ]

theorem loopBody_nuOk (A B : VTy) : (loopBody A B).NuOk :=
  ⟨⟨VTy.poly_of_not_occ (VTy.not_occ_rename_succ A), trivial⟩,
   VTy.poly_of_not_occ (VTy.not_occ_rename_succ B)⟩

theorem delayBody_nuOk (A : VTy) : (delayBody A).NuOk := loopBody_nuOk A .unit

theorem instT_effOf (S' : VTy) : ∀ (S : List OpSig) (R : VTy),
    instT S' (CTy.effOf S R) = CTy.effOf S (VTy.inst S' R)
  | [], _ => rfl
  | o :: S, R => by simp only [CTy.effOf, instT, instT_effOf S' S R]

theorem effLeaf_effOf {S : List OpSig} (hS : ∀ o ∈ S, o.A.Cl 0 ∧ o.B.Cl 0) {R : VTy}
    (hR : R.Poly) : EffLeaf (CTy.effOf S R) := by
  induction S with
  | nil => exact hR
  | cons o S ih =>
      exact ⟨(hS o (by simp)).1, (hS o (by simp)).2, ih fun o' h => hS o' (by simp [h])⟩

theorem nuLeaf_effOf {S : List OpSig} (hS : ∀ o ∈ S, o.A.Cl 0 ∧ o.B.Cl 0) {R : VTy}
    (hR : R.Poly) : NuLeaf (CTy.effOf S R) := by
  cases S with
  | nil => exact hR
  | cons o S => exact effLeaf_effOf hS hR

theorem loopEffBody_nuOk {S : List OpSig} (hS : ∀ o ∈ S, o.A.Cl 0 ∧ o.B.Cl 0) (A B : VTy) :
    (loopEffBody S A B).NuOk :=
  ⟨nuLeaf_effOf hS ⟨VTy.poly_of_not_occ (VTy.not_occ_rename_succ A), trivial⟩,
   nuLeaf_effOf hS (VTy.poly_of_not_occ (VTy.not_occ_rename_succ B))⟩

theorem loopEffBody_instT (S : List OpSig) (A B S' : VTy) :
    (loopEffBody S A B).instT S' = .amp (CTy.effOf S (.sum A S')) (CTy.effOf S B) := by
  simp only [instT, instT_effOf, inst_sum_var, VTy.inst_rename_succ]

theorem streamBody_nuOk (A : VTy) : (streamBody A).NuOk :=
  ⟨⟨VTy.poly_of_not_occ (VTy.not_occ_rename_succ A), trivial⟩, fun h => h⟩

theorem iterBody_nuOk (A R R' : VTy) : (iterBody A R R').NuOk :=
  ⟨⟨⟨VTy.poly_of_not_occ (VTy.not_occ_rename_succ A), trivial⟩,
    VTy.poly_of_not_occ (VTy.not_occ_rename_succ R)⟩,
   VTy.poly_of_not_occ (VTy.not_occ_rename_succ R')⟩

end CTy

/-- The unrolling of `Loop A B`: `F(A ⊕ U(Loop A B)) & F B`. -/
abbrev loopUnroll (A B : VTy) : CTy := .amp (.ret (.sum A (.thunk (.loop A B)))) (.ret B)

/-- The unrolling of `D A`: `F(A ⊕ U(D A)) & F 1`. -/
abbrev delayUnroll (A : VTy) : CTy := .amp (.ret (.sum A (.thunk (.delay A)))) (.ret .unit)

/-- The unrolling of `Stream A`: `F(A ⊗ U(Stream A)) & F 1`. -/
abbrev streamUnroll (A : VTy) : CTy := .amp (.ret (.tensor A (.thunk (.stream A)))) (.ret .unit)

/-- The unrolling of `Iter A R R'`: `F((A ⊗ U(Iter A R R')) ⊕ R) & F R'`. -/
abbrev iterUnroll (A R R' : VTy) : CTy :=
  .amp (.ret (.sum (.tensor A (.thunk (.iter A R R'))) R)) (.ret R')

theorem CTy.loop_unroll (A B : VTy) : (CTy.loopBody A B).unroll = loopUnroll A B :=
  CTy.loopBody_instT A B _

theorem CTy.delay_unroll (A : VTy) : (CTy.delayBody A).unroll = delayUnroll A :=
  CTy.delayBody_instT A _

theorem CTy.stream_unroll (A : VTy) : (CTy.streamBody A).unroll = streamUnroll A :=
  CTy.streamBody_instT A _

theorem CTy.iter_unroll (A R R' : VTy) : (CTy.iterBody A R R').unroll = iterUnroll A R R' :=
  CTy.iterBody_instT A R R' _

/-! ### Free lifetime variables under type substitution -/

theorem vFree_rename {y : LifeVar} : ∀ (A : VTy) (r : Nat → Nat), VFree y (A.rename r) ↔ VFree y A
  | .unit, _ => Iff.rfl
  | .tensor A B, r => or_congr (vFree_rename A r) (vFree_rename B r)
  | .zero, _ => Iff.rfl
  | .sum A B, r => or_congr (vFree_rename A r) (vFree_rename B r)
  | .thunk _, _ => Iff.rfl
  | .ref A, r => vFree_rename A r
  | .imm _ A, r => or_congr Iff.rfl (vFree_rename A r)
  | .mut _ A, r => or_congr Iff.rfl (vFree_rename A r)
  | .box _ A, r => or_congr Iff.rfl (vFree_rename A r)
  | .bang A, r => vFree_rename A r
  | .fam A, r => vFree_rename A r
  | .unk, _ => Iff.rfl
  | .int _, _ => Iff.rfl
  | .opq _, _ => Iff.rfl
  | .tvar _, _ => Iff.rfl
  | .mu A, r => vFree_rename A (VTy.upR r)

theorem vFree_subst {y : LifeVar} : ∀ (A : VTy) (σ : Nat → VTy),
    VFree y (A.subst σ) → VFree y A ∨ ∃ n, VFree y (σ n)
  | .unit, _, h => h.elim
  | .tensor A B, σ, h => h.elim
      (fun h => (vFree_subst A σ h).elim (fun h => Or.inl (Or.inl h)) Or.inr)
      (fun h => (vFree_subst B σ h).elim (fun h => Or.inl (Or.inr h)) Or.inr)
  | .zero, _, h => h.elim
  | .sum A B, σ, h => h.elim
      (fun h => (vFree_subst A σ h).elim (fun h => Or.inl (Or.inl h)) Or.inr)
      (fun h => (vFree_subst B σ h).elim (fun h => Or.inl (Or.inr h)) Or.inr)
  | .thunk _, _, h => Or.inl h
  | .ref A, σ, h => vFree_subst A σ h
  | .imm _ A, σ, h => h.elim (fun h => Or.inl (Or.inl h))
      (fun h => (vFree_subst A σ h).elim (fun h => Or.inl (Or.inr h)) Or.inr)
  | .mut _ A, σ, h => h.elim (fun h => Or.inl (Or.inl h))
      (fun h => (vFree_subst A σ h).elim (fun h => Or.inl (Or.inr h)) Or.inr)
  | .box _ A, σ, h => h.elim (fun h => Or.inl (Or.inl h))
      (fun h => (vFree_subst A σ h).elim (fun h => Or.inl (Or.inr h)) Or.inr)
  | .bang A, σ, h => vFree_subst A σ h
  | .fam A, σ, h => vFree_subst A σ h
  | .unk, _, h => h.elim
  | .int _, _, h => h.elim
  | .opq _, _, h => h.elim
  | .tvar n, _, h => Or.inr ⟨n, h⟩
  | .mu A, σ, h => by
      rcases vFree_subst A (VTy.upS σ) h with h | ⟨n, hn⟩
      · exact Or.inl h
      · cases n with
        | zero => exact hn.elim
        | succ n => exact Or.inr ⟨n, (vFree_rename (σ n) Nat.succ).mp hn⟩

theorem vFree_subst_of {y : LifeVar} : ∀ (A : VTy) (σ : Nat → VTy), VFree y A → VFree y (A.subst σ)
  | .unit, _, h => h
  | .tensor A B, σ, h => h.elim (fun h => Or.inl (vFree_subst_of A σ h))
      (fun h => Or.inr (vFree_subst_of B σ h))
  | .zero, _, h => h
  | .sum A B, σ, h => h.elim (fun h => Or.inl (vFree_subst_of A σ h))
      (fun h => Or.inr (vFree_subst_of B σ h))
  | .thunk _, _, h => h
  | .ref A, σ, h => vFree_subst_of A σ h
  | .imm _ A, σ, h => h.elim Or.inl (fun h => Or.inr (vFree_subst_of A σ h))
  | .mut _ A, σ, h => h.elim Or.inl (fun h => Or.inr (vFree_subst_of A σ h))
  | .box _ A, σ, h => h.elim Or.inl (fun h => Or.inr (vFree_subst_of A σ h))
  | .bang A, σ, h => vFree_subst_of A σ h
  | .fam A, σ, h => vFree_subst_of A σ h
  | .unk, _, h => h
  | .int _, _, h => h
  | .opq _, _, h => h
  | .tvar _, _, h => h.elim
  | .mu A, σ, h => vFree_subst_of A (VTy.upS σ) h

/-- `A[S/X]`'s free lifetime variables are `A`'s and `S`'s. -/
theorem vFree_inst {y : LifeVar} {S A : VTy} (h : VFree y (VTy.inst S A)) : VFree y A ∨ VFree y S := by
  rcases vFree_subst A (VTy.scons S .tvar) h with h | ⟨n, hn⟩
  · exact Or.inl h
  · cases n with
    | zero => exact Or.inr hn
    | succ n => exact hn.elim

theorem vFree_immG {y : LifeVar} (b : Lifetime.Life) : ∀ (A : VTy) (pay : Nat → VTy),
    VFree y (VTy.immG b pay A) → b.mentions y = true ∨ VFree y A ∨ ∃ n, VFree y (pay n)
  | .unit, _, h => h.elim
  | .tensor A B, pay, h => h.elim
      (fun h => (vFree_immG b A pay h).elim Or.inl
        (fun h => h.elim (fun h => Or.inr (Or.inl (Or.inl h))) (fun h => Or.inr (Or.inr h))))
      (fun h => (vFree_immG b B pay h).elim Or.inl
        (fun h => h.elim (fun h => Or.inr (Or.inl (Or.inr h))) (fun h => Or.inr (Or.inr h))))
  | .zero, _, h => h.elim
  | .sum A B, pay, h => h.elim
      (fun h => (vFree_immG b A pay h).elim Or.inl
        (fun h => h.elim (fun h => Or.inr (Or.inl (Or.inl h))) (fun h => Or.inr (Or.inr h))))
      (fun h => (vFree_immG b B pay h).elim Or.inl
        (fun h => h.elim (fun h => Or.inr (Or.inl (Or.inr h))) (fun h => Or.inr (Or.inr h))))
  | .thunk _, _, h => h.elim
  | .ref A, pay, h => h.elim Or.inl (fun h => (vFree_subst A pay h).elim
      (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h)))
  | .imm _ A, pay, h => h.elim (fun h => Or.inr (Or.inl (Or.inl h)))
      (fun h => (vFree_subst A pay h).elim
        (fun h => Or.inr (Or.inl (Or.inr h))) (fun h => Or.inr (Or.inr h)))
  | .mut _ A, pay, h => h.elim Or.inl (fun h => (vFree_subst A pay h).elim
      (fun h => Or.inr (Or.inl (Or.inr h))) (fun h => Or.inr (Or.inr h)))
  | .box _ A, pay, h => (vFree_immG b A pay h).elim Or.inl
      (fun h => h.elim (fun h => Or.inr (Or.inl (Or.inr h))) (fun h => Or.inr (Or.inr h)))
  | .bang A, pay, h => (vFree_subst A pay h).elim
      (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
  | .fam A, pay, h => (vFree_immG b A pay h).elim Or.inl
      (fun h => h.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h)))
  | .unk, _, h => h.elim
  | .int _, _, h => h.elim
  | .opq _, _, h => h.elim
  | .tvar _, _, h => h.elim
  | .mu A, pay, h => by
      rcases vFree_immG b A _ h with h | h | ⟨n, hn⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · cases n with
        | zero =>
            rcases vFree_subst (.mu A) pay hn with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        | succ n => exact Or.inr (Or.inr ⟨n, hn⟩)

/-! ### The reborrow metafunction -/

/-- `Imm̲ 'b A`: the view a load through an immutable borrow at `'b` gives of a payload of
type `A`.  `1`, `0`, `⊗`, `⊕` structurally; `U C ↦ Unk` (codata has no safe view, as `⊸`
and `∀` in BoLo); `Ref A ↦ Imm 'b A`; `Imm @a A` kept; `Mut @a A ↦ Imm 'b A`;
`[@a] A ↦ Imm̲ 'b A`; `!A` kept whole (it holds no resource); `Unk ↦ Unk`; `[L] ↦ [Imm̲ 'b L]`
(`[spec §9]`).  At `μX. A` the
clause substitutes inside the payloads it keeps (`VTy.immG`, `docs/scope-recursion.md` §2.4):
`Imm̲ 'b (μX. A) = μY. Imm̲ᵡ 'b A`, a head `X` becoming `Y` and a payload `X` becoming `μX. A`.  `[spec §6]` -/
def VTy.immReborrow (b : Lifetime.Life) : VTy → VTy
  | .unit => .unit
  | .tensor A B => .tensor (A.immReborrow b) (B.immReborrow b)
  | .zero => .zero
  | .sum A B => .sum (A.immReborrow b) (B.immReborrow b)
  | .thunk _ => .unk
  | .ref A => .imm b A
  | .imm a A => .imm a A
  | .mut _ A => .imm b A
  | .box _ A => A.immReborrow b
  | .bang A => .bang A
  | .fam A => .fam (A.immReborrow b)
  | .unk => .unk
  | .int w => .int w
  | .opq _ => .unk
  | .tvar n => .tvar n
  | .mu A => .mu (VTy.immG b (VTy.scons (.mu A) .tvar) A)

/-- `Imm̲` is `immG` at the identity payload substitution. -/
theorem VTy.immReborrow_eq_immG (b : Lifetime.Life) : ∀ A : VTy, A.immReborrow b = VTy.immG b .tvar A
  | .unit => rfl
  | .tensor A B => by
      simp only [VTy.immReborrow, VTy.immG, VTy.immReborrow_eq_immG b A, VTy.immReborrow_eq_immG b B]
  | .zero => rfl
  | .sum A B => by
      simp only [VTy.immReborrow, VTy.immG, VTy.immReborrow_eq_immG b A, VTy.immReborrow_eq_immG b B]
  | .thunk _ => rfl
  | .ref A => by simp only [VTy.immReborrow, VTy.immG, VTy.subst_id]
  | .imm _ A => by simp only [VTy.immReborrow, VTy.immG, VTy.subst_id]
  | .mut _ A => by simp only [VTy.immReborrow, VTy.immG, VTy.subst_id]
  | .box _ A => by simp only [VTy.immReborrow, VTy.immG, VTy.immReborrow_eq_immG b A]
  | .bang A => by simp only [VTy.immReborrow, VTy.immG, VTy.subst_id]
  | .fam A => by simp only [VTy.immReborrow, VTy.immG, VTy.immReborrow_eq_immG b A]
  | .unk => rfl
  | .int _ => rfl
  | .opq _ => rfl
  | .tvar _ => rfl
  | .mu A => by simp only [VTy.immReborrow, VTy.immG, VTy.subst_id]

/-- On closed types `Imm̲` is `immReb`. -/
theorem VTy.immReborrow_eq_immReb (b : Lifetime.Life) {A : VTy} (h : A.Cl 0) :
    A.immReborrow b = VTy.immReb b A := by
  rw [VTy.immReborrow_eq_immG, VTy.immReb]
  exact VTy.immG_congr b A h (fun n hn => absurd hn (Nat.not_lt_zero _))

theorem VTy.Cl_immReborrow (b : Lifetime.Life) {A : VTy} (h : A.Cl 0) :
    (A.immReborrow b).Cl 0 := by
  rw [VTy.immReborrow_eq_immReb b h]
  exact VTy.Cl_immG b A VTy.dflt (fun _ => trivial) h

/-- **The unrolling law of `Imm̲` at a closed `μ`.** -/
theorem VTy.immReborrow_unroll (b : Lifetime.Life) {T : VTy} (hT : T.Cl 1) :
    (VTy.inst (.mu T) T).immReborrow b
      = VTy.inst ((VTy.mu T).immReborrow b) (VTy.immX b T) := by
  have hmu : (VTy.mu T).Cl 0 := hT
  rw [VTy.immReborrow_eq_immReb b (VTy.Cl_inst hmu hT), VTy.immReborrow_eq_immReb b hmu,
    VTy.immReb_unroll b hT]

/-- `Imm̲ 'b (μX.T) = μY. Imm̲ᵡ 'b T` at a closed `μ`. -/
theorem VTy.immReborrow_mu (b : Lifetime.Life) {T : VTy} (hT : T.Cl 1) :
    (VTy.mu T).immReborrow b = .mu (VTy.immX b T) := by
  rw [VTy.immReborrow_eq_immReb b (show (VTy.mu T).Cl 0 from hT), VTy.immReb_mu b hT]

theorem VTy.immReborrow_unroll' (b : Lifetime.Life) {T : VTy} (hT : T.Cl 1) :
    (VTy.inst (.mu T) T).immReborrow b = VTy.inst (.mu (VTy.immX b T)) (VTy.immX b T) := by
  rw [VTy.immReborrow_unroll b hT, VTy.immReborrow_mu b hT]

theorem VTy.Cl_immX (b : Lifetime.Life) {T : VTy} (hT : T.Cl 1) : (VTy.immX b T).Cl 1 :=
  VTy.Cl_immG b T _ (VTy.scons_closed (show (VTy.mu T).Cl 0 from hT) (fun _ => trivial)) hT

theorem VTy.noMut_immX (b : Lifetime.Life) {T : VTy} (hT : T.Cl 1) (k : Nat) :
    (VTy.immX b T).NoMut k :=
  VTy.noMut_immG b T _ (VTy.scons_closed (show (VTy.mu T).Cl 0 from hT) (fun _ => trivial))

/-! ### Lifetime substitution -/

mutual
/-- One past the largest lifetime index anywhere in `A`, binders included. -/
def VTy.lifeBound : VTy → Nat
  | .unit => 0
  | .zero => 0
  | .unk => 0
  | .int _ => 0
  | .opq _ => 0
  | .tensor A B => max A.lifeBound B.lifeBound
  | .sum A B => max A.lifeBound B.lifeBound
  | .thunk C => C.lifeBound
  | .ref A => A.lifeBound
  | .bang A => A.lifeBound
  | .fam A => A.lifeBound
  | .imm a A => max a.varBound A.lifeBound
  | .mut a A => max a.varBound A.lifeBound
  | .box a A => max a.varBound A.lifeBound
  | .tvar _ => 0
  | .mu A => A.lifeBound
/-- One past the largest lifetime index anywhere in `C`, binders included. -/
def CTy.lifeBound : CTy → Nat
  | .ret A => A.lifeBound
  | .arr A C => max A.lifeBound C.lifeBound
  | .amp C D => max C.lifeBound D.lifeBound
  | .top => 0
  | .all x b C => max (x + 1) (max b.varBound C.lifeBound)
  | .nu C => C.lifeBound
  | .eff _ _ _ A B fin _ C => max A.lifeBound (max B.lifeBound (max fin.lifeBound C.lifeBound))
end

mutual
/-- `A` with the simultaneous lifetime substitution `σ` applied. -/
def VTy.applyLSub (σ : LSubst) : VTy → VTy
  | .unit => .unit
  | .zero => .zero
  | .unk => .unk
  | .int w => .int w
  | .opq k => .opq k
  | .tensor A B => .tensor (A.applyLSub σ) (B.applyLSub σ)
  | .sum A B => .sum (A.applyLSub σ) (B.applyLSub σ)
  | .thunk C => .thunk (C.applyLSub σ)
  | .ref A => .ref (A.applyLSub σ)
  | .bang A => .bang (A.applyLSub σ)
  | .fam A => .fam (A.applyLSub σ)
  | .imm a A => .imm (a.applySub σ) (A.applyLSub σ)
  | .mut a A => .mut (a.applySub σ) (A.applyLSub σ)
  | .box a A => .box (a.applySub σ) (A.applyLSub σ)
  | .tvar n => .tvar n
  | .mu A => .mu (A.applyLSub σ)
/-- `C` with the simultaneous lifetime substitution `σ` applied, renaming a `∀` binder where
it would capture (`Ty.applyLSub`'s `∀` clause). -/
def CTy.applyLSub (σ : LSubst) : CTy → CTy
  | .ret A => .ret (A.applyLSub σ)
  | .arr A C => .arr (A.applyLSub σ) (C.applyLSub σ)
  | .amp C D => .amp (C.applyLSub σ) (D.applyLSub σ)
  | .top => .top
  | .all y b C =>
      if lsubCaptures (lsubDrop σ y) y then
        .all (max (y + 1) (max (lsubRangeBound (lsubDrop σ y)) C.lifeBound)) (b.applySub σ)
          (C.applyLSub ((y, Lifetime.Life.var
            (max (y + 1) (max (lsubRangeBound (lsubDrop σ y)) C.lifeBound))) :: lsubDrop σ y))
      else
        .all y (b.applySub σ) (C.applyLSub (lsubDrop σ y))
  | .nu C => .nu (C.applyLSub σ)
  | .eff n i q A B fin rc C =>
      .eff n i q (A.applyLSub σ) (B.applyLSub σ) (fin.applyLSub σ) rc (C.applyLSub σ)
end

/-- `A[@a/'x]`. -/
def VTy.instLife (x : LifeVar) (a : Lifetime.Life) (A : VTy) : VTy := A.applyLSub [(x, a)]

/-- `C[@a/'x]` — the substitution `∀E` performs. -/
def CTy.instLife (x : LifeVar) (a : Lifetime.Life) (C : CTy) : CTy := C.applyLSub [(x, a)]

theorem CTy.applyLSub_all_captures {σ : LSubst} {y : LifeVar} {b : Lifetime.Life} {C : CTy}
    (h : lsubCaptures (lsubDrop σ y) y = true) :
    (CTy.all y b C).applyLSub σ
      = .all (max (y + 1) (max (lsubRangeBound (lsubDrop σ y)) C.lifeBound)) (b.applySub σ)
          (C.applyLSub ((y, Lifetime.Life.var
            (max (y + 1) (max (lsubRangeBound (lsubDrop σ y)) C.lifeBound))) :: lsubDrop σ y)) := by
  rw [CTy.applyLSub, if_pos h]

theorem CTy.applyLSub_all_not_captures {σ : LSubst} {y : LifeVar} {b : Lifetime.Life} {C : CTy}
    (h : lsubCaptures (lsubDrop σ y) y = false) :
    (CTy.all y b C).applyLSub σ = .all y (b.applySub σ) (C.applyLSub (lsubDrop σ y)) := by
  rw [CTy.applyLSub, if_neg (by simp [h])]

mutual
/-- A variable free in `A` is below `A.lifeBound`. -/
theorem lt_vLifeBound {x : LifeVar} : ∀ {A : VTy}, VFree x A → x < A.lifeBound
  | .unit, h => h.elim
  | .zero, h => h.elim
  | .unk, h => h.elim
  | .int _, h => h.elim
  | .opq _, h => h.elim
  | .tensor A B, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_right _ _)
  | .sum A B, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_right _ _)
  | .thunk C, h => lt_cLifeBound (C := C) h
  | .ref A, h => lt_vLifeBound (A := A) h
  | .bang A, h => lt_vLifeBound (A := A) h
  | .fam A, h => lt_vLifeBound (A := A) h
  | .imm a A, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_varBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_right _ _)
  | .mut a A, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_varBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_right _ _)
  | .box a A, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_varBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_right _ _)
  | .tvar _, h => h.elim
  | .mu A, h => lt_vLifeBound (A := A) h
/-- A variable free in `C` is below `C.lifeBound`. -/
theorem lt_cLifeBound {x : LifeVar} : ∀ {C : CTy}, CFree x C → x < C.lifeBound
  | .ret A, h => lt_vLifeBound (A := A) h
  | .arr A C, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_cLifeBound h) (Nat.le_max_right _ _)
  | .amp C D, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_cLifeBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_cLifeBound h) (Nat.le_max_right _ _)
  | .top, h => h.elim
  | .all y b C, h => by
      rcases h with h | ⟨-, h⟩
      · exact Nat.lt_of_lt_of_le (lt_varBound h)
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      · exact Nat.lt_of_lt_of_le (lt_cLifeBound h)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  | .nu C, h => lt_cLifeBound (C := C) h
  | .eff _ _ _ A B fin _ C, h => by
      rcases h with h | h | h | h
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h)
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      · exact Nat.lt_of_lt_of_le (lt_cLifeBound h)
          (Nat.le_trans (Nat.le_max_left _ _)
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
      · exact Nat.lt_of_lt_of_le (lt_cLifeBound h)
          (Nat.le_trans (Nat.le_max_right _ _)
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
end

/-- `Imm̲` introduces only its index. -/
theorem vFree_immReborrow {x y : LifeVar} : ∀ (A : VTy),
    VFree y (A.immReborrow (.var x)) → y = x ∨ VFree y A := by
  intro A
  induction A using VTy.recV with
  | unit => intro h; exact h.elim
  | zero => intro h; exact h.elim
  | unk => intro h; exact h.elim
  | int _ => intro h; exact h.elim
  | opq _ => intro h; exact h.elim
  | thunk C => intro h; exact h.elim
  | tensor A B ihA ihB =>
      rintro (h | h)
      · rcases ihA h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases ihB h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
  | sum A B ihA ihB =>
      rintro (h | h)
      · rcases ihA h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases ihB h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
  | ref A _ =>
      rintro (h | h)
      · left; simp only [Lifetime.Life.mentions, beq_iff_eq] at h; exact h
      · exact Or.inr h
  | imm a A _ => intro h; exact Or.inr h
  | «mut» a A _ =>
      rintro (h | h)
      · left; simp only [Lifetime.Life.mentions, beq_iff_eq] at h; exact h
      · exact Or.inr (Or.inr h)
  | box a A ih =>
      intro h
      rcases ih h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  | bang A _ => intro h; exact Or.inr h
  | fam L ih => intro h; exact ih h
  | tvar _ => intro h; exact h.elim
  | mu A _ =>
      intro h
      rcases vFree_immG (.var x) A _ h with h | h | ⟨n, hn⟩
      · left; simp only [Lifetime.Life.mentions, beq_iff_eq] at h; exact h
      · exact Or.inr h
      · cases n with
        | zero => exact Or.inr hn
        | succ n => exact hn.elim

/-! ### Outlives and scoping -/

/-- The outlives judgment on value types with the box rule's lifetime premise `Rb b` and the
`Imm`/`Mut` rules' premise `Rr b`: `[TR]` p. 2's rules (`OutlivesRules`), with `0` outliving
every lifetime (it has no values), and `μ` checked at its body. `VOutlives` and `VOutlivesLe`
are its two instances.  `[spec §23]` -/
inductive VOutlivesR (Rb Rr : Lifetime.Life → Prop) : VTy → Prop where
  | unit : VOutlivesR Rb Rr .unit
  | tensor {A B} : VOutlivesR Rb Rr A → VOutlivesR Rb Rr B → VOutlivesR Rb Rr (.tensor A B)
  | zero : VOutlivesR Rb Rr .zero
  | sum {A B} : VOutlivesR Rb Rr A → VOutlivesR Rb Rr B → VOutlivesR Rb Rr (.sum A B)
  | ref {A} : VOutlivesR Rb Rr A → VOutlivesR Rb Rr (.ref A)
  | bang {A} : VOutlivesR Rb Rr (.bang A)
  | box {b A} : Rb b → VOutlivesR Rb Rr (.box b A)
  | imm {b A} : Rr b → VOutlivesR Rb Rr (.imm b A)
  | «mut» {b A} : Rr b → VOutlivesR Rb Rr (.mut b A)
  /-- A type variable is read under its `μ`, whose body is checked with the variable
  outliving `@a`. -/
  | tvar {n} : VOutlivesR Rb Rr (.tvar n)
  /-- `Δ ⊢ μX. A ⊐ @a` from `A ⊐ @a` with `X ⊐ @a` (`docs/scope-recursion.md` §2.3:
  `X` holds only what `A` holds). -/
  | mu {A} : VOutlivesR Rb Rr A → VOutlivesR Rb Rr (.mu A)
  /-- `I32`/`I64` outlive every lifetime.  `[spec §8]` -/
  | int {w} : VOutlivesR Rb Rr (.int w)
  | opq {k} : VOutlivesR Rb Rr (.opq k)
  /-- `Δ ⊢ [L] ⊐ @a` from `Δ ⊢ L ⊐ @a`.  `[spec §9]` -/
  | fam {L} : VOutlivesR Rb Rr L → VOutlivesR Rb Rr (.fam L)

/-- `Δ ⊢ A ⊐ @a`: the box rule from `Δ ⊨ @a ⊑ @b`, an extension of 2.35, sound because a
`[@b] A` value's resource is already in `Res_β ⊆ Res_α` (`vC_outlives`); the `Imm`/`Mut` rules
from `Δ ⊨ @a ⊏ @b`, as printed.  `[spec §23]` -/
abbrev VOutlives (Δ : LifeCtx) (a : Lifetime.Life) : VTy → Prop :=
  VOutlivesR (Δ.EntailsLe a) (Δ.EntailsLt a)

/-- `Δ ⊢ A ⊒ @a`: all three lifetime premises `Δ ⊨ @a ⊑ @b`, the side condition of the borrows
that lend a payload `mut`. It gives every stratum strictly below `α` (`vC_outlivesLe`), not
`Res_α`.  `[spec §23]` -/
abbrev VOutlivesLe (Δ : LifeCtx) (a : Lifetime.Life) : VTy → Prop :=
  VOutlivesR (Δ.EntailsLe a) (Δ.EntailsLe a)

/-- `Δ ⊨ @a ⊏ @b` gives `Δ ⊨ @a ⊑ @b`. -/
theorem entailsLe_of_entailsLt {Δ : LifeCtx} {a b : Lifetime.Life} (h : Δ.EntailsLt a b) :
    Δ.EntailsLe a b := fun δ hδ => by
  obtain ⟨m, n, hm, hn, hlt⟩ := h δ hδ
  refine ⟨m, n, hm, hn, ?_⟩
  simp only [Lifetime.SLife.Lt, Lifetime.SLife.Le] at hlt ⊢; omega

theorem VOutlivesR.mono {Rb Rr Rb' Rr' : Lifetime.Life → Prop} (hb : ∀ b, Rb b → Rb' b)
    (hr : ∀ b, Rr b → Rr' b) {A : VTy} (h : VOutlivesR Rb Rr A) : VOutlivesR Rb' Rr' A := by
  induction h with
  | unit => exact .unit
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂
  | zero => exact .zero
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  | ref _ ih => exact .ref ih
  | bang => exact .bang
  | box h => exact .box (hb _ h)
  | imm h => exact .imm (hr _ h)
  | «mut» h => exact .mut (hr _ h)
  | tvar => exact .tvar
  | mu _ ih => exact .mu ih
  | int => exact .int
  | opq => exact .opq
  | fam _ ih => exact .fam ih

/-- Every `Δ ⊢ A ⊐ @a` is a `Δ ⊢ A ⊒ @a`.  `[spec §23]` -/
theorem VOutlives.toLe {Δ : LifeCtx} {a : Lifetime.Life} {A : VTy} (h : VOutlives Δ a A) :
    VOutlivesLe Δ a A :=
  VOutlivesR.mono (fun _ h => h) (fun _ h => entailsLe_of_entailsLt h) h

theorem VOutlivesR.rename {Rb Rr : Lifetime.Life → Prop} {A : VTy} (h : VOutlivesR Rb Rr A) :
    ∀ r : Nat → Nat, VOutlivesR Rb Rr (A.rename r) := by
  induction h with
  | unit => intro _; exact .unit
  | tensor _ _ ih₁ ih₂ => intro r; exact .tensor (ih₁ r) (ih₂ r)
  | zero => intro _; exact .zero
  | sum _ _ ih₁ ih₂ => intro r; exact .sum (ih₁ r) (ih₂ r)
  | ref _ ih => intro r; exact .ref (ih r)
  | bang => intro _; exact .bang
  | fam _ ih => intro r; exact .fam (ih r)
  | box h => intro _; exact .box h
  | imm h => intro _; exact .imm h
  | «mut» h => intro _; exact .mut h
  | tvar => intro _; exact .tvar
  | mu _ ih => intro r; exact .mu (ih _)
  | int => intro _; exact .int
  | opq => intro _; exact .opq

theorem VOutlivesR.subst {Rb Rr : Lifetime.Life → Prop} {A : VTy} (h : VOutlivesR Rb Rr A) :
    ∀ σ : Nat → VTy, (∀ n, VOutlivesR Rb Rr (σ n)) → VOutlivesR Rb Rr (A.subst σ) := by
  induction h with
  | unit => intro _ _; exact .unit
  | tensor _ _ ih₁ ih₂ => intro σ hσ; exact .tensor (ih₁ σ hσ) (ih₂ σ hσ)
  | zero => intro _ _; exact .zero
  | sum _ _ ih₁ ih₂ => intro σ hσ; exact .sum (ih₁ σ hσ) (ih₂ σ hσ)
  | ref _ ih => intro σ hσ; exact .ref (ih σ hσ)
  | bang => intro _ _; exact .bang
  | fam _ ih => intro σ hσ; exact .fam (ih σ hσ)
  | box h => intro _ _; exact .box h
  | imm h => intro _ _; exact .imm h
  | «mut» h => intro _ _; exact .mut h
  | tvar => intro σ hσ; exact hσ _
  | int => intro _ _; exact .int
  | opq => intro _ _; exact .opq
  | mu _ ih =>
      intro σ hσ
      exact .mu (ih _ (fun n => by
        cases n with
        | zero => exact .tvar
        | succ n => exact (hσ n).rename Nat.succ))

/-- An outlives judgment at `μX. A` holds at its unrolling. -/
theorem VOutlivesR.unroll {Rb Rr : Lifetime.Life → Prop} {A : VTy}
    (h : VOutlivesR Rb Rr (.mu A)) : VOutlivesR Rb Rr (VTy.inst (.mu A) A) := by
  cases h with
  | mu hA => exact hA.subst _ (fun n => by
      cases n with
      | zero => exact .mu hA
      | succ n => exact .tvar)

theorem VOutlives.rename {Δ : LifeCtx} {a : Lifetime.Life} {A : VTy} (h : VOutlives Δ a A)
    (r : Nat → Nat) : VOutlives Δ a (A.rename r) := VOutlivesR.rename h r

theorem VOutlives.subst {Δ : LifeCtx} {a : Lifetime.Life} {A : VTy} (h : VOutlives Δ a A)
    (σ : Nat → VTy) (hσ : ∀ n, VOutlives Δ a (σ n)) : VOutlives Δ a (A.subst σ) :=
  VOutlivesR.subst h σ hσ

theorem VOutlives.unroll {Δ : LifeCtx} {a : Lifetime.Life} {A : VTy}
    (h : VOutlives Δ a (.mu A)) : VOutlives Δ a (VTy.inst (.mu A) A) := VOutlivesR.unroll h

theorem VOutlivesLe.unroll {Δ : LifeCtx} {a : Lifetime.Life} {A : VTy}
    (h : VOutlivesLe Δ a (.mu A)) : VOutlivesLe Δ a (VTy.inst (.mu A) A) := VOutlivesR.unroll h

/-- `Δ ⊨ Γ ⊐ @a`: `@a` is defined under `Δ` and every live slot outlives it (`Ctx.Outlives`). -/
def CtxOutlives (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) : Prop :=
  Δ.Defines a ∧ ∀ s ∈ Γ, s.live = true → VOutlives Δ a s.ty

/-- `A` is scoped in `Δ`: its free lifetime variables are in `dom(Δ)`. -/
def VScoped (Δ : LifeCtx) (A : VTy) : Prop := ∀ y, VFree y A → ∃ u, Δ.find? y = some u

/-! ### The borrow axioms' types

`[TR]` p. 3's axiom table read call-by-value (`VTy.lolli`, `VTy.all`), at arbitrary value-type
payloads. -/

/-- `swap : Ref A ⊸ B ⊸ Ref B ⊗ A`. -/
def axSwapTy (A B : VTy) : VTy := .lolli (.ref A) (.lolli B (.tensor (.ref B) A))

/-- `copy : Imm @a A ⊸ Imm @a A ⊗ Imm @a A`. -/
def axCopyTy (a : Lifetime.Life) (A : VTy) : VTy :=
  .lolli (.imm a A) (.tensor (.imm a A) (.imm a A))

/-- `forget : Imm @a A ⊸ 1`. -/
def axForgetImmTy (a : Lifetime.Life) (A : VTy) : VTy := .lolli (.imm a A) .unit

/-- `forget : Mut @a A ⊸ 1`. -/
def axForgetMutTy (a : Lifetime.Life) (A : VTy) : VTy := .lolli (.mut a A) .unit

/-- `forget : Unk ⊸ 1`. -/
def axForgetUnkTy : VTy := .lolli .unk .unit

/-- `withbor : Ref A ⊸ (∀'x ⊏ @bnd. Imm 'x A ⊸ ['x] B) ⊸ Ref A ⊗ B`. -/
def axWithbor1Ty (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.ref A)
    (.lolli (.all x bnd (.lolli (.imm (.var x) A) (.box (.var x) B))) (.tensor (.ref A) B))

/-- `withbor : Ref A ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ ['x] B) ⊸ Ref A ⊗ B`. -/
def axWithbor2Ty (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.ref A)
    (.lolli (.all x bnd (.lolli (.mut (.var x) A) (.box (.var x) B))) (.tensor (.ref A) B))

/-- `withbor : Mut @a A ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ ['x] B) ⊸ Mut @a A ⊗ B`. -/
def axWithbor3Ty (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.mut a A)
    (.lolli (.all x bnd (.lolli (.mut (.var x) A) (.box (.var x) B))) (.tensor (.mut a A) B))

/-- `withload : Imm @a A ⊸ (∀'x ⊏ @bnd. Imm̲ 'x A ⊸ ['x] B) ⊸ B`. -/
def axWithloadTy (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.imm a A)
    (.lolli (.all x bnd (.lolli (VTy.immReborrow (.var x) A) (.box (.var x) B))) B)

/-- `withswap : Mut @a A ⊸ (A ⊸ A ⊗ B) ⊸ Mut @a A ⊗ B`. -/
def axWithswapTy (a : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.mut a A) (.lolli (.lolli A (.tensor A B)) (.tensor (.mut a A) B))

end BoCa.Fig16.LogRel.Core

end
