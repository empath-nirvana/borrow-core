import Core.Classes
import Core.Tok
import Core.EffPrograms
import Core.Demonic

/-!
# Core — declared types that is not consumable  `[spec §11, §12, §42]`

A declared type that is not consumable `N` with payload `A` is `A ⊗ Tok` (SPEC §42), `Tok` the token
of `Core/Tok.lean`: a location owning a unit cell, made by `mint` and consumed by `burn`. No new
type former and no new class: `N` is a linear type that is not consumable.

| fact | statement |
|---|---|
| `Tok` is linear and not consumable | `tok_linear` |
| a field that is not consumable makes its container linear with none | `not_consumable_tensor_left`, `_right`, `_sum_left`, `_right`, `_box`, `_ref`, `_array`, `_mu_body`, `_mu_key`, and the `not_persistent_*` lemmas |
| `N` is linear and not consumable | `decl_linear` |
| a borrow of `N` is linear and consumable: a loan ends, `N` is not consumed | `decl_imm_consume`, `decl_mut_consume` |
| an abort cannot abandon `N` | `decl_not_ownFree` (`[let]`'s `hW`, `[raise]`'s `hd`) |
| `mint` allocates the token's cell; `burn` frees it | `mint_step`, `burn_step` |
| the entry discards `main`'s result by its consume, which a declared type has none of | `entry_derives`, `entry_runs`, `entry_decl_not_consumable` |

The guarantee is `N`'s linearity: used exactly once, never copied or consumed by the checker, never
abandoned at an abort. Which function consumes it is the program's choice. Every run ends with every
cell freed (`adequacyC`), the token's among them.

The checker inserts a consume only at a `consume` node, which carries `Consumable` (`TDerivesP.consume_consumable`,
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

/-- **`Tok` is linear and not consumable.**  `[spec §11, §12]` -/
theorem tok_linear : Linear tokTy ∧ ¬ Consumable tokTy :=
  ⟨by simp [Linear, VTy.Persistent, VTy.persistent], fun h => nomatch h⟩

/-- `Tok` holds an owned cell: an abort cannot abandon it. -/
theorem tok_not_ownFree : ¬ tokTy.OwnFree := by
  intro h; cases h with
  | opq _ hk => exact Opaque.tok_not_host hk

theorem not_consumable_tensor_right {A B : VTy} (h : ¬ Consumable B) : ¬ Consumable (.tensor A B) := by
  intro h'; cases h' with | tensor _ hB => exact h hB

theorem not_consumable_tensor_left {A B : VTy} (h : ¬ Consumable A) : ¬ Consumable (.tensor A B) := by
  intro h'; cases h' with | tensor hA _ => exact h hA

theorem not_consumable_sum_right {A B : VTy} (h : ¬ Consumable B) : ¬ Consumable (.sum A B) := by
  intro h'; cases h' with | sum _ hB => exact h hB

theorem not_consumable_sum_left {A B : VTy} (h : ¬ Consumable A) : ¬ Consumable (.sum A B) := by
  intro h'; cases h' with | sum hA _ => exact h hA

theorem not_consumable_box {a : Lifetime.Life} {A : VTy} (h : ¬ Consumable A) : ¬ Consumable (.box a A) := by
  intro h'; cases h' with | box hA => exact h hA

theorem not_consumable_ref {A : VTy} (h : ¬ Consumable A) : ¬ Consumable (.ref A) := by
  intro h'; cases h' with | ref hA => exact h hA

/-- An array of a type that is not consumable has none. -/
theorem not_consumable_array {A : VTy} (h : ¬ Consumable A) : ¬ Consumable (.fam (.ref A)) := by
  intro h'; cases h' with | array hA => exact h hA

/-- At `μX. A`: the body, its recursive positions at the consume's results, is not consumable. -/
theorem not_consumable_mu_body {A : VTy} (h : ¬ Consumable (FoldP.resO consumeAlgs [A] A)) :
    ¬ Consumable (.mu A) := by
  intro h'; cases h' with | mu _ hA _ _ => exact h hA

/-- At `μX. A`: a key of the body (`keysIn`) whose body is not consumable. -/
theorem not_consumable_mu_key {A B : VTy} {Bs : FoldP.Stack}
    (hm : FoldP.Bnd.mu (B :: Bs) ∈ FoldP.keysIn [A] A)
    (h : ¬ Consumable (FoldP.resO consumeAlgs (B :: Bs) B)) : ¬ Consumable (.mu A) := by
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

/-- **A declared type is linear and not consumable.**  `[spec §12, §42]` -/
theorem decl_linear (A : VTy) : Linear (declTy A) ∧ ¬ Consumable (declTy A) :=
  ⟨not_persistent_tensor_right tok_linear.1, not_consumable_tensor_right tok_linear.2⟩

/-- **A declared value cannot be abandoned at an abort**: `[let]`'s `hW` and `[raise]`'s `hd` ask
for `OwnFree`.  `[spec §19, §42]` -/
theorem decl_not_ownFree (A : VTy) : ¬ (declTy A).OwnFree :=
  not_ownFree_tensor_right tok_not_ownFree

/-- **A shared borrow of a declared value is linear and consumable**: the loan ends; the
value is not consumed.  `[spec §12, §42]` -/
theorem decl_imm_consume (a : Lifetime.Life) (A : VTy) : LinearConsumable (.imm a (declTy A)) :=
  ⟨by simp [Linear, VTy.Persistent, VTy.persistent], .imm⟩

/-- **A mutable borrow of a declared value is linear and consumable.**  `[spec §12, §42]` -/
theorem decl_mut_consume (a : Lifetime.Life) (A : VTy) : LinearConsumable (.mut a (declTy A)) :=
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

/-! ### The entry: `main`'s result discarded by its consume

A program's entry discards `main`'s result by its consume (`consumeSlot_derives`), not by leaving it
to the host: `x <- main; consumeE A x; return ()`. It is a derivation exactly when the result has a
consume; at a declared type it has none (`decl_linear`), so no rule consumes it.  `[spec §42]` -/

/-- The entry around `main : F A`: `x <- e; consumeE A x; return ()`. -/
def entryE (A : VTy) (e : Expr) : Expr := .app (.val (.lam (consumeSlotE A 0 (.val .unit)))) e

/-- **The entry is a derivation at a result that is consumable.**  `[spec §42]` -/
theorem entry_derives {Δ : LifeCtx} {e : Expr} {A : VTy}
    (h : CDerives Δ [] e (.comp (.ret A))) (hA : Consumable A) :
    CDerives Δ [] (entryE A e) (.comp (.ret .unit)) :=
  .bind .nil h (consumeSlot_derives (Γ₁ := [⟨A, true⟩]) (Γ₂ := [⟨A, false⟩]) (.left .nil) (.here .nil) hA
    (.ret (.unitI (.cons .nil))))

/-- **The entry frees every cell**: from the empty memory it runs to `()` at the empty memory
(`adequacyC` at `entry_derives`), so a result that is consumable is freed, not left to the
host.  `[spec §42]` -/
theorem entry_runs {e : Expr} {A : VTy} (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    (hA : Consumable A) :
    Steps Adequacy.emptyMem (entryE A e) Adequacy.emptyMem (.val .unit) :=
  adequacyC (entry_derives h hA)

/-- At a declared type the entry is not consumable to use: `main`'s result is refused. -/
theorem entry_decl_not_consumable (A : VTy) : ¬ Consumable (declTy A) := (decl_linear A).2

end BoCa.Fig16.LogRel.Core
