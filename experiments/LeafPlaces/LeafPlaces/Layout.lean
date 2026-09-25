import Places.Programs

/-!
# Unboxed structs as blocks of leaf locations

A struct type is a binary tree of fields (`Shape`); its leaves are the scalar fields.  One
allocation of a struct takes a **block** of `size σ` consecutive locations starting at a base
`b`, and the leaf at in-order position `i` lives at `b + i`: the block is the struct, laid out
contiguously.  A sub-struct at a node is the sub-block starting at `b` plus the sizes of the
leaves before it, so a place `s.a.x` is a base plus a static offset.

The handle of a struct is, in the source calculus, the tuple of its leaf addresses
(`Shape.addr b σ`).  The machine has no address arithmetic, so a single-word handle is a
lowering of that tuple; it is sound exactly when the tuple is `addr b σ` for some `b` — which
`LeafPlaces.Packed` states and the lemmas of `LeafPlaces/Packed.lean` maintain.

The typed handle is the leaf family: `refTy σ` is `Ref T₁ ⊗ …` in the shape of the tree, so a
struct handle and the tuple of its field handles have the same type (pack and unpack are the
identity), and `famTy M a σ` is the family of leaf borrows at one lifetime.

Leaf types are `plainB`: built from `1`, `⊕`, `⊗` and `Ref`.  They mention no lifetime, so they
are scoped everywhere, bind nothing, are fixed by lifetime substitution and outlive every
lifetime.
-/

noncomputable section

namespace BoCa.LeafPlaces
open BoCa BoCa.Lifetime

/-! ## Plain types -/

/-- Types built from `1`, `⊕`, `⊗` and `Ref`: no lifetime occurs in them. -/
def plainB : Ty → Bool
  | .unit => true
  | .sum T₁ T₂ => plainB T₁ && plainB T₂
  | .tensor T₁ T₂ => plainB T₁ && plainB T₂
  | .ref T => plainB T
  | _ => false

theorem plain_scoped {Δ : LifeCtx} : ∀ {T : Ty}, plainB T = true → T.scopedB Δ = true
  | .unit, _ => rfl
  | .sum _ _, h => by
      simp only [plainB, Bool.and_eq_true] at h
      simp [Ty.scopedB, plain_scoped h.1, plain_scoped h.2]
  | .tensor _ _, h => by
      simp only [plainB, Bool.and_eq_true] at h
      simp [Ty.scopedB, plain_scoped h.1, plain_scoped h.2]
  | .ref _, h => by simp only [plainB] at h; simp [Ty.scopedB, plain_scoped h]

theorem plain_binds {x : LifeVar} : ∀ {T : Ty}, plainB T = true → T.bindsB x = false
  | .unit, _ => rfl
  | .sum _ _, h => by
      simp only [plainB, Bool.and_eq_true] at h
      simp [Ty.bindsB, plain_binds h.1, plain_binds h.2]
  | .tensor _ _, h => by
      simp only [plainB, Bool.and_eq_true] at h
      simp [Ty.bindsB, plain_binds h.1, plain_binds h.2]
  | .ref _, h => by simp only [plainB] at h; simp [Ty.bindsB, plain_binds h]

theorem plain_lsub {τ : LSubst} : ∀ {T : Ty}, plainB T = true → T.applyLSub τ = T
  | .unit, _ => rfl
  | .sum _ _, h => by
      simp only [plainB, Bool.and_eq_true] at h
      simp [Ty.applyLSub, plain_lsub h.1, plain_lsub h.2]
  | .tensor _ _, h => by
      simp only [plainB, Bool.and_eq_true] at h
      simp [Ty.applyLSub, plain_lsub h.1, plain_lsub h.2]
  | .ref _, h => by simp only [plainB] at h; simp [Ty.applyLSub, plain_lsub h]

theorem plain_outlives {Δ : LifeCtx} {a : Life} : ∀ {T : Ty}, plainB T = true → OutlivesRules Δ a T
  | .unit, _ => .unit
  | .sum _ _, h => by
      simp only [plainB, Bool.and_eq_true] at h
      exact .sum (plain_outlives h.1) (plain_outlives h.2)
  | .tensor _ _, h => by
      simp only [plainB, Bool.and_eq_true] at h
      exact .tensor (plain_outlives h.1) (plain_outlives h.2)
  | .ref _, h => by simp only [plainB] at h; exact .ref (plain_outlives h)

/-! ## Shapes -/

/-- A struct type: a binary tree whose leaves are the scalar fields.  `{a : A, b : B}` is
`node (leaf A) (leaf B)`; a nested struct is a nested node. -/
inductive Shape where
  | leaf (T : Ty)
  | node (s₁ s₂ : Shape)
  deriving Repr

namespace Shape

/-- Every leaf type is plain. -/
def plain : Shape → Bool
  | .leaf T => plainB T
  | .node s₁ s₂ => plain s₁ && plain s₂

/-- The number of leaves: the number of locations of a block. -/
def size : Shape → Nat
  | .leaf _ => 1
  | .node s₁ s₂ => size s₁ + size s₂

/-- The typed handle: the leaf family `Ref T₁ ⊗ …`, in the shape of the tree. -/
def refTy : Shape → Ty
  | .leaf T => .ref T
  | .node s₁ s₂ => .tensor (refTy s₁) (refTy s₂)

/-- The struct's value: its leaves' values, in the shape of the tree. -/
def valTy : Shape → Ty
  | .leaf T => T
  | .node s₁ s₂ => .tensor (valTy s₁) (valTy s₂)

/-- The family of leaf borrows `M @a T₁ ⊗ …` at one lifetime `@a`. -/
def famTy (M : Life → Ty → Ty) (a : Life) : Shape → Ty
  | .leaf T => M a T
  | .node s₁ s₂ => .tensor (famTy M a s₁) (famTy M a s₂)

/-- The handle of the block at base `b`: leaf `i` (in order) at `b + i`. -/
def addr (b : Loc) : Shape → Val
  | .leaf _ => .loc b
  | .node s₁ s₂ => .pair (addr b s₁) (addr (b + size s₁) s₂)

theorem size_pos : ∀ σ : Shape, 0 < σ.size
  | .leaf _ => Nat.one_pos
  | .node s₁ _ => Nat.lt_of_lt_of_le (size_pos s₁) (Nat.le_add_right _ _)

theorem refTy_plain : ∀ {σ : Shape}, σ.plain = true → plainB σ.refTy = true
  | .leaf _, h => by simpa [plain, refTy, plainB] using h
  | .node _ _, h => by
      simp only [plain, Bool.and_eq_true] at h
      simp [refTy, plainB, refTy_plain h.1, refTy_plain h.2]

theorem valTy_plain : ∀ {σ : Shape}, σ.plain = true → plainB σ.valTy = true
  | .leaf _, h => by simpa [plain, valTy] using h
  | .node _ _, h => by
      simp only [plain, Bool.and_eq_true] at h
      simp [valTy, plainB, valTy_plain h.1, valTy_plain h.2]

end Shape

/-! ## The leaf formers `Mut` and `Imm`

What the family construction needs of the borrow former `M`: `Places.Borrows` (its `withbor`
typing and its `⊑` rule), and that `M` commutes with scoping, binders and substitution as the
constructors `.mut` and `.imm` do. -/

structure Former (M : Life → Ty → Ty) (side : LifeCtx → Ty → Prop) : Prop where
  bw : Places.Borrows M side
  scopedM : ∀ Δ a S, (M a S).scopedB Δ = (a.wf Δ && S.scopedB Δ)
  bindsM : ∀ a S z, (M a S).bindsB z = S.bindsB z
  lsubM : ∀ τ a S, (M a S).applyLSub τ = M (a.applySub τ) (S.applyLSub τ)
  side_plain : ∀ Δ S, plainB S = true → side Δ S

theorem formerMut :
    Former Places.mutM (fun Δ S => ∃ b, Δ.Defines b ∧ Outlives Δ S b) :=
  ⟨Places.borrowsMut, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ h => ⟨.top, LifeCtx.defines_of_wf rfl, plain_outlives h⟩⟩

theorem formerImm : Former Places.immM (fun _ _ => True) :=
  ⟨Places.borrowsImm, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => trivial⟩

namespace Shape
variable {M : Life → Ty → Ty} {side : LifeCtx → Ty → Prop}

theorem famTy_scoped (F : Former M side) {Δ : LifeCtx} {a : Life} (ha : a.wf Δ = true) :
    ∀ {σ : Shape}, σ.plain = true → (σ.famTy M a).scopedB Δ = true
  | .leaf _, h => by simp [famTy, F.scopedM, ha, plain_scoped (by simpa [plain] using h)]
  | .node _ _, h => by
      simp only [plain, Bool.and_eq_true] at h
      simp [famTy, Ty.scopedB, famTy_scoped F ha h.1, famTy_scoped F ha h.2]

theorem famTy_binds (F : Former M side) {a : Life} {z : LifeVar} :
    ∀ {σ : Shape}, σ.plain = true → (σ.famTy M a).bindsB z = false
  | .leaf _, h => by simp [famTy, F.bindsM, plain_binds (by simpa [plain] using h)]
  | .node _ _, h => by
      simp only [plain, Bool.and_eq_true] at h
      simp [famTy, Ty.bindsB, famTy_binds F h.1, famTy_binds F h.2]

theorem famTy_lsub (F : Former M side) {a : Life} {τ : LSubst} :
    ∀ {σ : Shape}, σ.plain = true → (σ.famTy M a).applyLSub τ = σ.famTy M (a.applySub τ)
  | .leaf _, h => by simp [famTy, F.lsubM, plain_lsub (by simpa [plain] using h)]
  | .node _ _, h => by
      simp only [plain, Bool.and_eq_true] at h
      simp [famTy, Ty.applyLSub, famTy_lsub F h.1, famTy_lsub F h.2]

end Shape

/-! ## The resource model at another location type

The resource model (`PMap`, cells, `ResU`, flattening, `↭`, `reb`) is generic in `Loc`.  The
typed world, the machine and the syntax use `BoCa.Loc = ℕ`, and the one property of `ℕ` they
use is that a finite list of locations misses one (`PMap.Infinite`, at allocation).  Below, three
of the model's results at `ℕ × List ℕ` — a block and a path — and that property there. -/

/-- `[TR]` 6.49 (`↭` is transitive) at `Loc = ℕ × List ℕ`. -/
theorem updV_trans_blockPath {ρ₁ ρ₂ ρ₃ : Fig16.ResU (ℕ × List ℕ) Val}
    (h₁ : ρ₁.UpdV ρ₂) (h₂ : ρ₂.UpdV ρ₃) : ρ₁.UpdV ρ₃ :=
  Fig16.ResU.UpdV.trans h₁ h₂

/-- `●` is associative at `Loc = ℕ × List ℕ`. -/
theorem compS_assoc_blockPath (ρ₁ ρ₂ ρ₃ w : Fig16.ResU (ℕ × List ℕ) Val) :
    (∃ x, Fig16.ResU.CompS ρ₂ ρ₃ x ∧ Fig16.ResU.CompS ρ₁ x w) ↔
      (∃ y, Fig16.ResU.CompS ρ₁ ρ₂ y ∧ Fig16.ResU.CompS y ρ₃ w) :=
  Fig16.ResU.CompS.assoc ρ₁ ρ₂ ρ₃ w

/-- Flattening is functional at `Loc = ℕ × List ℕ`. -/
theorem flat_functional_blockPath {ρ σ σ' : Fig16.ResU (ℕ × List ℕ) Val}
    (h : Fig16.ResU.Flat ρ σ) (h' : Fig16.ResU.Flat ρ σ') : σ = σ' :=
  Fig16.ResU.Flat.functional h h'

/-- A finite list of blocks and paths misses one: allocation's premise holds at `ℕ × List ℕ`. -/
theorem infinite_blockPath : Fig16.PMap.Infinite (ℕ × List ℕ) := by
  intro d
  refine ⟨((d.map Prod.fst).sum + 1, []), fun h => ?_⟩
  have : (d.map Prod.fst).sum + 1 ≤ (d.map Prod.fst).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem (f := Prod.fst) h)
  omega

end BoCa.LeafPlaces

end
