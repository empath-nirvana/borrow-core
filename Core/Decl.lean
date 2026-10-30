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
| no run ends with a declared value unconsumed | `tok_released`, `tok_released_every_run`, `adequacyC_tok` |

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

/-! ### No run ends with a declared value unconsumed

A declared value is consumed by `burn`, which frees its token's cell; one left unconsumed keeps the
cell. The token's cell is an `own` cell of the relation (`Opaque.rel .tok`), so the theorems that
every cell is freed (`adequacyC`, `adequacyD`, `leakFree_closed`) say that no token is left. -/

/-- A token is live in a memory at `ℓ`: the memory holds its cell. -/
def TokLive (μ : Heap) (ℓ : Loc) : Prop := μ ℓ = some .unit

/-- **No run ends with a declared value unconsumed.** On every run of a closed program of `F A`,
`A` unrestricted, that reaches a value, the final memory holds no token: every one minted was
burned.  `[spec §42]` -/
theorem tok_released {e : Expr} {A : VTy} (hA : A.Persistent)
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A))) {μ₁ : Heap} {w : Val}
    (hs : Steps Adequacy.emptyMem e μ₁ (.val w)) : ∀ ℓ, ¬ TokLive μ₁ ℓ := by
  obtain ⟨rfl, -⟩ := EffPrograms.leakFree_closed hA h hs
  intro ℓ hℓ; cases hℓ

/-- **Every token live on a run is released on it.** From every configuration a closed program of
`F 1` reaches, the run goes on to the empty memory, so every token that configuration holds is
burned on the way.  `[spec §42]` -/
theorem tok_released_every_run {e : Expr} (h : CDerives LifeCtx.empty [] e (.comp (.ret .unit)))
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem e μ₁ e₁) :
    Steps μ₁ e₁ Adequacy.emptyMem (.val .unit) ∧ ∀ ℓ, ¬ TokLive Adequacy.emptyMem ℓ :=
  ⟨adequacyD h hs, fun _ hℓ => by cases hℓ⟩

/-- **`adequacyC` leaves no token.** The run `adequacyC` gives ends with no token live.
`[spec §42]` -/
theorem adequacyC_tok {e : Expr} (h : CDerives LifeCtx.empty [] e (.comp (.ret .unit))) :
    Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) ∧
      ∀ ℓ, ¬ TokLive Adequacy.emptyMem ℓ :=
  ⟨adequacyC h, fun _ hℓ => by cases hℓ⟩

end BoCa.Fig16.LogRel.Core
