import Core.Classes
import Core.Tok
import Core.EffPrograms
import Core.Demonic

/-!
# Core — declared types with no derived drop  `[spec §11, §12, §42]`

A declared type with no derived drop `N` with payload `A` is `A ⊗ Tok` (SPEC §42), `Tok` the token
of `Core/Tok.lean`: a location owning a unit cell, made by `mint` and released by `burn`. No new
type former and no new class: `N` is a linear type with no derived drop.

| fact | statement |
|---|---|
| `Tok` is linear with no derived drop | `tok_linear` |
| a field with no derived drop makes its container linear with none | `not_hasDtor_tensor_left`, `_right`, `_sum_left`, `_right`, `_box`, `_ref`, `_array`, `_mu_body`, `_mu_key`, and the `not_persistent_*` lemmas |
| `N` is linear with no derived drop | `decl_linear` |
| a borrow of `N` is linear with a derived drop: a loan ends, `N` is not consumed | `decl_imm_drop`, `decl_mut_drop` |
| an abort cannot abandon `N` | `decl_not_ownFree` (`[let]`'s `hW`, `[raise]`'s `hd`) |
| `mint` allocates the token's cell; `burn` frees it | `mint_step`, `burn_step` |
| the entry discards `main`'s result by its derived drop, which a declared type has none of | `entry_derives`, `entry_runs`, `entry_decl_no_drop` |

| every cell a `mint` step allocates is released later by a `burn` step (stated, not proved) | `decl_consumed`; on the current machine `decl_consumed_mintE_at_ref` |

`decl_consumed` is a `Prop`, not a theorem: `mint` and `burn` are λs over `alloc` and `free`, and
`Tok`'s relation is `Ref 1`'s, so neither the step relation nor the model tells a token's cell
from a `Ref 1`'s. `decl_consumed_mintE_at_ref` is a closed typed program on whose run a `mint`
step's cell is released by `free` (SPEC §42, *Open*).

The checker inserts a drop only at a `dtor` node, which carries `HasDtor` (`TDerivesP.dtor_hasDtor`,
`Frontend/Check/TDerives.lean`), so it inserts none at `N`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head)
open BoCa.Lifetime (LifeCtx)

/-! ### Classes -/

/-- **`Tok` is linear with no derived drop.**  `[spec §11, §12]` -/
theorem tok_linear : Linear tokTy ∧ ¬ HasDtor tokTy :=
  ⟨by simp [Linear, VTy.Persistent, VTy.persistent], fun h => nomatch h⟩

/-- `Tok` holds an owned cell: an abort cannot abandon it. -/
theorem tok_not_ownFree : ¬ tokTy.OwnFree := by
  intro h; cases h with
  | opq _ hk => exact Opaque.tok_not_host hk

theorem not_hasDtor_tensor_right {A B : VTy} (h : ¬ HasDtor B) : ¬ HasDtor (.tensor A B) := by
  intro h'; cases h' with | tensor _ hB => exact h hB

theorem not_hasDtor_tensor_left {A B : VTy} (h : ¬ HasDtor A) : ¬ HasDtor (.tensor A B) := by
  intro h'; cases h' with | tensor hA _ => exact h hA

theorem not_hasDtor_sum_right {A B : VTy} (h : ¬ HasDtor B) : ¬ HasDtor (.sum A B) := by
  intro h'; cases h' with | sum _ hB => exact h hB

theorem not_hasDtor_sum_left {A B : VTy} (h : ¬ HasDtor A) : ¬ HasDtor (.sum A B) := by
  intro h'; cases h' with | sum hA _ => exact h hA

theorem not_hasDtor_box {a : Lifetime.Life} {A : VTy} (h : ¬ HasDtor A) : ¬ HasDtor (.box a A) := by
  intro h'; cases h' with | box hA => exact h hA

theorem not_hasDtor_ref {A : VTy} (h : ¬ HasDtor A) : ¬ HasDtor (.ref A) := by
  intro h'; cases h' with | ref hA => exact h hA

/-- An array of a type with no derived drop has none. -/
theorem not_hasDtor_array {A : VTy} (h : ¬ HasDtor A) : ¬ HasDtor (.fam (.ref A)) := by
  intro h'; cases h' with | array hA => exact h hA

/-- At `μX. A`: the body, its recursive positions at the destructor's results, has no derived drop. -/
theorem not_hasDtor_mu_body {A : VTy} (h : ¬ HasDtor (FoldP.resO dtorAlgs [A] A)) :
    ¬ HasDtor (.mu A) := by
  intro h'; cases h' with | mu _ hA _ _ => exact h hA

/-- At `μX. A`: a key of the body (`keysIn`) whose body has no derived drop. -/
theorem not_hasDtor_mu_key {A B : VTy} {Bs : FoldP.Stack}
    (hm : FoldP.Bnd.mu (B :: Bs) ∈ FoldP.keysIn [A] A)
    (h : ¬ HasDtor (FoldP.resO dtorAlgs (B :: Bs) B)) : ¬ HasDtor (.mu A) := by
  intro h'; cases h' with | mu _ _ hmu _ => exact h (hmu B Bs hm)

theorem not_persistent_tensor_right {A B : VTy} (h : ¬ B.Persistent) :
    ¬ (VTy.tensor A B).Persistent := by
  simp_all [VTy.Persistent, VTy.persistent]

theorem not_persistent_tensor_left {A B : VTy} (h : ¬ A.Persistent) :
    ¬ (VTy.tensor A B).Persistent := by
  simp_all [VTy.Persistent, VTy.persistent]

theorem not_persistent_sum_right {A B : VTy} (h : ¬ B.Persistent) : ¬ (VTy.sum A B).Persistent := by
  simp_all [VTy.Persistent, VTy.persistent]

theorem not_persistent_sum_left {A B : VTy} (h : ¬ A.Persistent) : ¬ (VTy.sum A B).Persistent := by
  simp_all [VTy.Persistent, VTy.persistent]

theorem not_persistent_box {a : Lifetime.Life} {A : VTy} (h : ¬ A.Persistent) :
    ¬ (VTy.box a A).Persistent := by
  simp_all [VTy.Persistent, VTy.persistent]

theorem not_persistent_ref (A : VTy) : ¬ (VTy.ref A).Persistent := by
  simp [VTy.Persistent, VTy.persistent]

theorem not_persistent_array (A : VTy) : ¬ (VTy.fam (.ref A)).Persistent := by
  simp [VTy.Persistent, VTy.persistent]

theorem not_persistent_mu {A : VTy} (h : ¬ A.Persistent) : ¬ (VTy.mu A).Persistent := by
  simp_all [VTy.Persistent, VTy.persistent]

/-- A type holding `Tok` is not `OwnFree` (`OwnFree` is conjunctive at `⊗` and `⊕`). -/
theorem not_ownFree_tensor_right {A B : VTy} (h : ¬ B.OwnFree) : ¬ (VTy.tensor A B).OwnFree := by
  intro h'; cases h' with | tensor _ hB => exact h hB

theorem not_ownFree_tensor_left {A B : VTy} (h : ¬ A.OwnFree) : ¬ (VTy.tensor A B).OwnFree := by
  intro h'; cases h' with | tensor hA _ => exact h hA

theorem not_ownFree_sum_right {A B : VTy} (h : ¬ B.OwnFree) : ¬ (VTy.sum A B).OwnFree := by
  intro h'; cases h' with | sum _ hB => exact h hB

theorem not_ownFree_sum_left {A B : VTy} (h : ¬ A.OwnFree) : ¬ (VTy.sum A B).OwnFree := by
  intro h'; cases h' with | sum hA _ => exact h hA

/-- A declared type with payload `A`.  `[spec §42]` -/
abbrev declTy (A : VTy) : VTy := .tensor A tokTy

/-- **A declared type is linear with no derived drop.**  `[spec §12, §42]` -/
theorem decl_linear (A : VTy) : Linear (declTy A) ∧ ¬ HasDtor (declTy A) :=
  ⟨not_persistent_tensor_right tok_linear.1, not_hasDtor_tensor_right tok_linear.2⟩

/-- **A declared value cannot be abandoned at an abort**: `[let]`'s `hW` and `[raise]`'s `hd` ask
for `OwnFree`.  `[spec §19, §42]` -/
theorem decl_not_ownFree (A : VTy) : ¬ (declTy A).OwnFree :=
  not_ownFree_tensor_right tok_not_ownFree

/-- **A shared borrow of a declared value is linear with a derived drop**: the loan ends; the
value is not consumed.  `[spec §12, §42]` -/
theorem decl_imm_drop (a : Lifetime.Life) (A : VTy) : DerivedDrop (.imm a (declTy A)) :=
  ⟨by simp [Linear, VTy.Persistent, VTy.persistent], .imm⟩

/-- **A mutable borrow of a declared value is linear with a derived drop.**  `[spec §12, §42]` -/
theorem decl_mut_drop (a : Lifetime.Life) (A : VTy) : DerivedDrop (.mut a (declTy A)) :=
  ⟨by simp [Linear, VTy.Persistent, VTy.persistent], .mut⟩

/-! ### `mint` and `burn` on the machine -/

/-- **`mint ()` allocates the token's cell**, at any location the memory does not hold. -/
theorem mint_step (μ : Heap) (ℓ : Loc) (h : μ ℓ = none) :
    Steps μ (.app mintE (.val .unit)) (μ.upd ℓ .unit) (.val (.loc ℓ)) :=
  .more (Step1.head (Head.beta μ _ _)) (.more (Step1.head (Head.alloc μ .unit ℓ h)) (.refl _ _))

/-- **`burn ℓ` frees the token's cell.** -/
theorem burn_step (μ : Heap) (ℓ : Loc) (h : μ ℓ = some .unit) :
    Steps μ (.app burnE (.val (.loc ℓ))) (μ.del ℓ) (.val .unit) :=
  .more (Step1.head (Head.beta μ _ _)) (.more (Step1.head (Head.free μ ℓ .unit h)) (.refl _ _))

/-! ### The entry: `main`'s result discarded by its derived drop

A program's entry discards `main`'s result by its derived drop (`drop_derives`), not by leaving it
to the host: `x <- main; dtorE A x; return ()`. It is a derivation exactly when the result has a
derived drop; at a declared type it has none (`decl_linear`), so no rule consumes it.  `[spec §42]` -/

/-- The entry around `main : F A`: `x <- e; dtorE A x; return ()`. -/
def entryE (A : VTy) (e : Expr) : Expr := .app (.val (.lam (dropE A 0 (.val .unit)))) e

/-- **The entry is a derivation at a result with a derived drop.**  `[spec §42]` -/
theorem entry_derives {Δ : LifeCtx} {e : Expr} {A : VTy}
    (h : CDerives Δ [] e (.comp (.ret A))) (hA : HasDtor A) :
    CDerives Δ [] (entryE A e) (.comp (.ret .unit)) :=
  .bind .nil h (drop_derives (Γ₁ := [⟨A, true⟩]) (Γ₂ := [⟨A, false⟩]) (.left .nil) (.here .nil) hA
    (.ret (.unitI (.cons .nil))))

/-- **The entry frees every cell**: from the empty memory it runs to `()` at the empty memory
(`adequacyC` at `entry_derives`), so a result with a derived drop is freed, not left to the
host.  `[spec §42]` -/
theorem entry_runs {e : Expr} {A : VTy} (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    (hA : HasDtor A) :
    Steps Adequacy.emptyMem (entryE A e) Adequacy.emptyMem (.val .unit) :=
  adequacyC (entry_derives h hA)

/-- At a declared type the entry has no derived drop to use: `main`'s result is refused. -/
theorem entry_decl_no_drop (A : VTy) : ¬ HasDtor (declTy A) := (decl_linear A).2

/-! ### Every token minted is burned: the statement

A run is the list of its configurations `c 0, …, c n`, each a step of the one before (`IsRun`):
`Steps` keeps only its two ends, and the statement counts steps. A `mint` at `i` allocating `ℓ`
is `mint ()`'s β at step `i` and its `alloc` of `ℓ` at step `i + 1`; a `burn` of `ℓ` at `j` is
`burn ℓ`'s β at step `j` and its `free` of `ℓ` at step `j + 1` (`mint_step`, `burn_step`).

`decl_consumed` is stated, not proved (SPEC §42, *Open*). The fact a proof needs is that a cell
a `mint` step allocates is released by no step but a `burn` step's `free`, and neither the step
relation nor the model carries it: `mint` and `burn` are λs over `alloc` and `free`, a step
reads only its redex, and `Tok`'s relation is `Ref 1`'s (`vCE_tok_eq_ref`), so `fundamentalC`
gives a typed program nothing that tells a token's cell from a `Ref 1`'s. `mintE`'s code is also
a derivation at `1 ⊸ Ref 1` by the ordinary rules (`mintE_derives_ref`), and the closed program
`free (mintE ())` is a run on which a `mint` step's cell is released by a bare `free`
(`decl_consumed_mintE_at_ref`). -/

/-- `c 0, …, c n` is a run: each configuration is a step of the one before. -/
def IsRun (c : Nat → Heap × Expr) (n : Nat) : Prop :=
  ∀ i < n, Step1 (c i).1 (c i).2 (c (i + 1)).1 (c (i + 1)).2

/-- Steps `i` and `i + 1` of `c` are a `mint`: `mint ()`'s β, then the `alloc` of `ℓ`. -/
def MintsAt (c : Nat → Heap × Expr) (i : Nat) (ℓ : Loc) : Prop :=
  ∃ K : BoLo.Kont, (c i).2 = K.plug (.app mintE (.val .unit)) ∧
    (c (i + 1)).2 = K.plug (.app (.val (.prim .alloc)) (.val .unit)) ∧
    (c (i + 2)).2 = K.plug (.val (.loc ℓ)) ∧ (c (i + 2)).1 = (c (i + 1)).1.upd ℓ .unit

/-- Steps `j` and `j + 1` of `c` are a `burn` of `ℓ`: `burn ℓ`'s β, then the `free` of `ℓ`. -/
def BurnsAt (c : Nat → Heap × Expr) (j : Nat) (ℓ : Loc) : Prop :=
  ∃ K : BoLo.Kont, (c j).2 = K.plug (.app burnE (.val (.loc ℓ))) ∧
    (c (j + 1)).2 = K.plug (.app (.val (.prim .free)) (.val (.loc ℓ))) ∧
    (c (j + 2)).2 = K.plug (.val .unit) ∧ (c (j + 2)).1 = (c (j + 1)).1.del ℓ

/-- **Every token minted is burned** (the target; SPEC §42, *Open*): on every run of a closed
program of `F 1` from the empty memory to a value, each `mint` step allocating `ℓ` is followed,
later on the same run, by a `burn` step releasing `ℓ`.  `[spec §42]` -/
def decl_consumed : Prop :=
  ∀ (e : Expr), CDerives LifeCtx.empty [] e (.comp (.ret .unit)) →
    ∀ (c : Nat → Heap × Expr) (n : Nat) (w : Val),
      c 0 = (Adequacy.emptyMem, e) → IsRun c n → (c n).2 = .val w →
      ∀ i ℓ, i + 2 ≤ n → MintsAt c i ℓ → ∃ j, i + 2 ≤ j ∧ j + 2 ≤ n ∧ BurnsAt c j ℓ

/-- `mintE`'s code, `λx. alloc x`, is a derivation at `1 ⊸ Ref 1` by `thunkV`, `[λ]` and `⊸E` over
the `alloc` axiom, without `tokMint`. -/
theorem mintE_derives_ref {Δ : LifeCtx} : CDerives Δ [] mintE (.val (.lolli .unit (.ref .unit))) :=
  .thunkV rfl (.lam (.ret (.lolliE (Γ₁ := [⟨.unit, true⟩]) (Γ₂ := [⟨.unit, false⟩]) (.left .nil)
    (.var (.here .nil)) (.alloc (.cons .nil)))))

/-- `free (mintE ())`: `mintE`'s code at `1 ⊸ Ref 1`, its cell released by `free`. -/
def mintFreeE : Expr := .app (.val (.prim .free)) (.app mintE (.val .unit))

theorem mintFreeE_derives : CDerives LifeCtx.empty [] mintFreeE (.comp (.ret .unit)) :=
  .ret (.lolliE .nil (.lolliE .nil (.unitI .nil) mintE_derives_ref) (.free .nil))

/-- `mintFreeE`'s run: `mint ()`'s β, the `alloc` of `0`, the `free` of `0`. -/
def mintFreeRun : Nat → Heap × Expr
  | 0 => (Adequacy.emptyMem, mintFreeE)
  | 1 => (Adequacy.emptyMem, .app (.val (.prim .free)) (.app (.val (.prim .alloc)) (.val .unit)))
  | 2 => (Adequacy.emptyMem.upd 0 .unit, .app (.val (.prim .free)) (.val (.loc 0)))
  | _ => ((Adequacy.emptyMem.upd 0 .unit).del 0, .val .unit)

theorem mintFreeRun_isRun : IsRun mintFreeRun 3 := by
  intro i hi
  match i, hi with
  | 0, _ =>
    exact ⟨.appR (.val (.prim .free)) .hole, _, _, rfl, rfl, Head.beta _ _ _⟩
  | 1, _ =>
    exact ⟨.appR (.val (.prim .free)) .hole, _, _, rfl, rfl,
      Head.alloc _ _ 0 rfl⟩
  | 2, _ =>
    exact Step1.head (Head.free (Adequacy.emptyMem.upd 0 .unit) 0 .unit (BoLo.Heap.upd_same _ _ _))

/-- **`decl_consumed` does not hold of the current machine**: `mintFreeE` is a closed derivation
of `F 1`, its run from the empty memory reaches `()`, its first two steps are a `mint` of `0`, and
no `burn` step follows: the cell is released by `free`. This is the missing fact of
`decl_consumed` (SPEC §42, *Open*): nothing in the step relation or the model ties the cell of a
`mint` step to a `burn` step. -/
theorem decl_consumed_mintE_at_ref : ¬ decl_consumed (ℍ := ℍ) := by
  intro h
  obtain ⟨j, hj, hj', -⟩ := h mintFreeE mintFreeE_derives mintFreeRun 3 .unit rfl
    mintFreeRun_isRun rfl 0 0 (by omega)
    ⟨.appR (.val (.prim .free)) .hole, rfl, rfl, rfl, rfl⟩
  omega

end BoCa.Fig16.LogRel.Core
