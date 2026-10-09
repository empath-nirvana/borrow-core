import ProbeD1.Statement2
import Targets.Instance.Types

/-!
# ProbeD1 — statement 3, `[handle]` with a lend open, and statement 4, `[allR-E]` at W (DESIGN §7, §8)

* **`HandleRow p`**: Targets' `HandleCompat` (`Targets/I/Device.lean`) at `SemS`, at every stack.
  The handled body is read at `hideS (· == n) σ`: inside the handler no stop of `n` reaches a lend
  outside it, so its stops of `n` are at depth `0` (the lend open, the continuation re-lendable)
  and its other stops pass the handler frame to the lenders' row. That is GhostEnd's `effHandle`
  case (step 3f), with `AllCross` relaxed: `n` crosses no entry of the body's stack. The context
  is carried to the hidden stack by `MonoHide`, which statement 0's `MonoV` gives
  (`MonoHideFromMonoV`).
* **`ovalW p`**: the relation at the open types (RESTRUCTURE §4.2's `I.ovalW`) over W: at
  `U(∀ρ:k. C)` the intersection over the admissible rows on the same value, at every other type
  W's relation at the instance.
* **`AllREW p`**: `[allR-E]` at W, at every stack (with a lend open). **`AllRMono p`**: a value at
  `U(∀ρ:k. C)` made outside a borrow is one inside it: W's order through the intersection. These
  are what `reconB′` asks when it instantiates `retryR` inside its borrow's callback.

Statements only; no proofs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack TabAtS)
open Targets (RowEnv RowCon RVar)

/-! ### Statement 3 -/

/-- **`[handle]` at W, a lend open** (`HandleCompat` at `SemS`). -/
def HandleRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ Γr Γc : Ctx VTy) (e : Expr) (S : Row)
    (E : List (Qual × VTy × VTy)) (n : UInt32) (A R : VTy) (ir ic : Nat),
    Targets.Row.NU (Row.ofEff n E 0 ++ S) →
    Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.SplitP Γ₁ Γr Γc → Ctx.SoloP Γr ir (retTy S A R) →
    Ctx.SoloP Γc ic (clausesTy S R E) → n ≠ 0 → (∀ o ∈ S, o.n ≠ n) → E.length ≤ 2 ^ 32 →
    SemS p Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A)) →
    SemS p Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R))

/-- **Statement 3 at the placement `p`.** -/
def Statement3 (p : Placement) : Prop := HandleRow (ℍ := ℍ) p

/-! ### Statement 4 -/

/-- W's relation at `U` over a chain of row `∀`s: the intersection over the admissible rows. -/
def ovalU (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Targets.Inst.OCTy → RowEnv → Val → WProp
  | .allR ρ k C, η, v => fun r => ∀ s : Row, k.cls.Admits s → (∀ o ∈ s, k.adm o) →
      ovalU p σ δ αs ls C (Function.update η ρ s) v r
  | C, η, v => vRL p σ δ (.thunk (Targets.Inst.OCTy.den η C)) αs ls v

/-- **W's relation at the open types**: at `U(∀ρ:k. C)` and `!U(∀ρ:k. C)` the intersection over
the admissible rows on the same value, at every other type W's relation at the instance. -/
def ovalW (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Targets.Inst.OVTy → RowEnv → Val → WProp
  | .thunk C, η, v => ovalU p σ δ αs ls C η v
  | .bang A, η, v => fun r => r = PMap.empty ∧ ovalW p σ δ αs ls A η v r
  | A, η, v => vRL p σ δ (Targets.Inst.OVTy.den η A) αs ls v

/-- **`[allR-E]` at W**, at every stack: a value at `U(∀ρ:k. C)` is at `U C'` for every `C'` whose
instances are `C`'s at an admissible row family. -/
def AllREW (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (ρv : RVar) (k : RowCon)
    (C C' : Targets.Inst.OCTy) (η : RowEnv) (s : RowEnv → Row) (v : Val) (r : WRes),
    k.cls.Admits (s η) → (∀ o ∈ s η, k.adm o) →
    (∀ η', Targets.Inst.OCTy.den η' C' = Targets.Inst.OCTy.den (Function.update η' ρv (s η')) C) →
    ovalW p σ δ αs ls (.thunk (.allR ρv k C)) η v r → ovalW p σ δ αs ls (.thunk C') η v r

/-- **A row-polymorphic value made outside a borrow is one inside it**: W's order through the
intersection, at every instance. -/
def AllRMono (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls ls' : List SRec) (ρv : RVar) (k : RowCon)
    (C : Targets.Inst.OCTy) (η : RowEnv) (v : Val) (r : WRes) (σ' : LStack) (αs' : List Life),
    StackOK σ αs → Ext ls ls' r → Fut δ r (σ, αs) (σ', αs') →
    (∀ η', FutAvoidsV (Targets.Inst.OVTy.den η' (.thunk (.allR ρv k C))) σ σ') → TabAtS σ αs r →
    ovalW p σ δ αs ls (.thunk (.allR ρv k C)) η v r →
    ovalW p σ' δ αs' ls' (.thunk (.allR ρv k C)) η v r

/-- **Statement 4 at the placement `p`.** -/
def Statement4 (p : Placement) : Prop := AllREW (ℍ := ℍ) p ∧ AllRMono (ℍ := ℍ) p

end ProbeD1

end
