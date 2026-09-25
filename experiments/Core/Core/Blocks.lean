import Core.Folds

/-!
# Core — unboxed products as blocks of leaf cells

`experiments/LeafPlaces`' block view at this world's `VTy` and `wpTS`.  A product type is a
binary tree of fields (`Shape`); one allocation of it takes a block of `size σ` consecutive
locations from a base `b`, the leaf at in-order position `i` at `b + i`.

* **The handle is the leaf family.**  `refTy (leaf A) = Ref A` and
  `refTy (node s₁ s₂) = refTy s₁ ⊗ refTy s₂`, so the owned handle of a block of `A ⊗ B` has the
  type `Ref A ⊗ Ref B` by definition (`refTy_pair`).  Splitting a handle into its fields and
  pairing the fields of one block back into its handle are the identity on terms and on the
  relation (`packed_node`).
* **Allocation and free are derived terms** (`allocS`, `freeS`): leaf by leaf, typed by the
  existing `alloc`/`free` rules (`d_allocS`, `d_freeS`), so `fundamentalC` covers them.
* **Block allocation** (`wpTS_allocS`): at every frame the typed world admits, `allocS σ v` has
  a run placing the leaves at `b, b+1, …` for a base `b` above every allocated location, and
  returns `addr b σ`, packed.

The machine is unchanged (`Loc = ℕ`, one value per location).  A value names one location, so
a one-word handle is a lowering of the tuple `addr b σ`; it is sound for tuples that are a
block's.  A pair of leaf references from two different blocks has the same type
(`experiments/LeafPlaces`' `crossPack`); keeping such pairs from being formed is a checker rule.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Shapes -/

/-- An unboxed product: a binary tree whose leaves are the fields. -/
inductive Shape where
  | leaf (A : VTy)
  | node (s₁ s₂ : Shape)

namespace Shape

/-- The number of leaves: the number of locations of a block. -/
def size : Shape → Nat
  | .leaf _ => 1
  | .node s₁ s₂ => size s₁ + size s₂

/-- The owned handle: the leaf family `Ref A₁ ⊗ …`, in the shape of the tree. -/
def refTy : Shape → VTy
  | .leaf A => .ref A
  | .node s₁ s₂ => .tensor (refTy s₁) (refTy s₂)

/-- The product's value: its leaves' values, in the shape of the tree. -/
def valTy : Shape → VTy
  | .leaf A => A
  | .node s₁ s₂ => .tensor (valTy s₁) (valTy s₂)

/-- The handle of the block at base `b`: leaf `i` (in order) at `b + i`. -/
def addr (b : Loc) : Shape → Val
  | .leaf _ => .loc b
  | .node s₁ s₂ => .pair (addr b s₁) (addr (b + size s₁) s₂)

end Shape

/-- **The block handle of a pair is the pair of leaf handles**: `Ref (A ⊗ B)`, read as a block,
is `Ref A ⊗ Ref B`. -/
theorem refTy_pair (A B : VTy) :
    (Shape.node (.leaf A) (.leaf B)).refTy = .tensor (.ref A) (.ref B) := rfl

/-! ### Allocation and free, as terms -/

/-- `allocS (leaf A) = alloc`; `allocS (node s₁ s₂) = λv. let (v₁, v₂) = v in
(allocS s₁ v₁, allocS s₂ v₂)`. -/
def allocS : Shape → Expr
  | .leaf _ => .val (.prim .alloc)
  | .node s₁ s₂ => .val (.lam (.letpair (.var 0)
      (.pair (.app (allocS s₁) (.var 1)) (.app (allocS s₂) (.var 0)))))

/-- `freeS`: the same with `free`. -/
def freeS : Shape → Expr
  | .leaf _ => .val (.prim .free)
  | .node s₁ s₂ => .val (.lam (.letpair (.var 0)
      (.pair (.app (freeS s₁) (.var 1)) (.app (freeS s₂) (.var 0)))))

theorem allocS_closed : ∀ σ : Shape, closedAt 0 (allocS σ) = true
  | .leaf _ => rfl
  | .node s₁ s₂ => by
      simp only [allocS, Val.val_lam, closedAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, ⟨closedAt_mono _ (allocS_closed s₁) (by omega), by omega⟩,
        closedAt_mono _ (allocS_closed s₂) (by omega), by omega⟩

theorem freeS_closed : ∀ σ : Shape, closedAt 0 (freeS σ) = true
  | .leaf _ => rfl
  | .node s₁ s₂ => by
      simp only [freeS, Val.val_lam, closedAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, ⟨closedAt_mono _ (freeS_closed s₁) (by omega), by omega⟩,
        closedAt_mono _ (freeS_closed s₂) (by omega), by omega⟩

/-- `allocS σ : valTy σ ⊸ refTy σ`, from the `alloc` rule at every leaf. -/
theorem d_allocS : ∀ (σ : Shape) {Δ : LifeCtx} {Γ : Ctx VTy}, Ctx.Dead Γ →
    CDerives Δ Γ (allocS σ) (.val (.lolli σ.valTy σ.refTy))
  | .leaf _, _, _, hΓ => .alloc hΓ
  | .node s₁ s₂, _, _, hΓ =>
      .thunkV rfl (.lam (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ))
        (.ret (.tensorI (.right (.left (.dead (deadSplit hΓ))))
          (.lolliE (.dead (.left (.dead (deadSplit hΓ)))) (.var (.there (.here (.cons hΓ))))
            (d_allocS s₁ (.cons (.cons (.cons hΓ)))))
          (.lolliE (.left (.dead (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ))))
            (d_allocS s₂ (.cons (.cons (.cons hΓ)))))))))

/-- `freeS σ : refTy σ ⊸ valTy σ`, from the `free` rule at every leaf. -/
theorem d_freeS : ∀ (σ : Shape) {Δ : LifeCtx} {Γ : Ctx VTy}, Ctx.Dead Γ →
    CDerives Δ Γ (freeS σ) (.val (.lolli σ.refTy σ.valTy))
  | .leaf _, _, _, hΓ => .free hΓ
  | .node s₁ s₂, _, _, hΓ =>
      .thunkV rfl (.lam (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ))
        (.ret (.tensorI (.right (.left (.dead (deadSplit hΓ))))
          (.lolliE (.dead (.left (.dead (deadSplit hΓ)))) (.var (.there (.here (.cons hΓ))))
            (d_freeS s₁ (.cons (.cons (.cons hΓ)))))
          (.lolliE (.left (.dead (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ))))
            (d_freeS s₂ (.cons (.cons (.cons hΓ)))))))))

/-! ### The packed handle -/

/-- `𝒱⟦refTy σ⟧` at the handle of the block at `b`. -/
def Packed (σ : Shape) (b : Loc) (ls : List SRec) (δ : LSub) (v : Val) : WProp :=
  fun ρ => v = σ.addr b ∧ vP σ.refTy ls δ v ρ

/-- Split and join: a packed node is a packed handle of each child, at its sub-block, with the
same value and the resource split. -/
theorem packed_node {s₁ s₂ : Shape} {b : Loc} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes} :
    Packed (.node s₁ s₂) b ls δ v ρ ↔
      ∃ v₁ v₂ ρ₁ ρ₂, v = .pair v₁ v₂ ∧ ResU.CompS ρ₁ ρ₂ ρ ∧
        Packed s₁ b ls δ v₁ ρ₁ ∧ Packed s₂ (b + s₁.size) ls δ v₂ ρ₂ := by
  constructor
  · rintro ⟨rfl, v₁, v₂, h⟩
    obtain ⟨hv, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp h
    simp only [Shape.addr, Val.pair, Subtype.mk.injEq, Expr.pair.injEq] at hv
    have e₁ : v₁ = s₁.addr b := Subtype.ext hv.1.symm
    have e₂ : v₂ = s₂.addr (b + s₁.size) := Subtype.ext hv.2.symm
    subst e₁ e₂
    exact ⟨_, _, ρ₁, ρ₂, rfl, hc, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩⟩
  · rintro ⟨v₁, v₂, ρ₁, ρ₂, rfl, hc, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩⟩
    exact ⟨rfl, _, _, pure_sep_mk rfl ⟨ρ₁, ρ₂, hc, h₁, h₂⟩⟩

/-! ### `wpTS` at one frame -/

/-- The configuration `wpTS` quantifies over. -/
structure Cfg (ls : List SRec) (ρ ρf fρ : WRes) (ps : List FrameRec) : Prop where
  hash : ResU.Hash ρf ρ
  comp : ResU.CompS ρf ρ fρ
  tw : TW fρ ps (rsOf ls)
  tag : Tagged fρ ps ls

/-- `wpTS`'s body at the configuration `ρf ● ρ = fρ`. -/
def WpAt (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) (ρ ρf fρ : WRes)
    (ps : List FrameRec) : Prop :=
  ∃ (ρ' ρp fρ' fρ'p π : WRes) (v : Val) (μ μ' : Heap) (ps' : List FrameRec) (ls' : List SRec),
    ResU.Hash ρ' ρf ∧
    ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
    ResU.Lower fρ μ ∧
    ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
    Steps μ e μ' (.val v) ∧
    ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
    NoOwn ρp ∧
    TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
    (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' v ρ'

theorem wpTS_of_wpAt {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ∀ ρf fρ ps, Cfg ls ρ ρf fρ ps → WpAt ls e Q ρ ρf fρ ps) : wpTS ls e Q ρ :=
  fun ρf fρ ps hf hc hT htg => h ρf fρ ps ⟨hf, hc, hT, htg⟩

theorem wpAt_of_wpTS {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ ρf fρ : WRes}
    {ps : List FrameRec} (h : wpTS ls e Q ρ) (hc : Cfg ls ρ ρf fρ ps) : WpAt ls e Q ρ ρf fρ ps :=
  h ρf fρ ps hc.hash hc.comp hc.tw hc.tag

theorem wpAt_val {ls : List SRec} {v : Val} {Q : List SRec → Val → WProp} {ρ ρf fρ : WRes}
    {ps : List FrameRec} (hc : Cfg ls ρ ρf fρ ps) (hQ : Q ls v ρ) : WpAt ls (.val v) Q ρ ρf fρ ps :=
  wpAt_of_wpTS (wpTS_val ls v Q ρ hQ) hc

/-- A step that leaves memory alone, in front. -/
theorem wpAt_pure {ls : List SRec} {e e' : Expr} {Q : List SRec → Val → WProp} {ρ ρf fρ : WRes}
    {ps : List FrameRec} (hs : ∀ μ, Step1 μ e μ e') (h : WpAt ls e' Q ρ ρf fρ ps) :
    WpAt ls e Q ρ ρf fρ ps := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, h₁₅⟩ := h
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, .more (hs μ) h₇, h₈,
    h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅⟩

/-- `alloc v` at a chosen location `l` free in the whole configuration, under `K`. -/
theorem wpAt_alloc {ls : List SRec} {Q : List SRec → Val → WProp} {ρ ρf fρ : WRes}
    {ps : List FrameRec} {μ : Heap} (K : Kont) (v : Val) (l : Loc) (hc : Cfg ls ρ ρf fρ ps)
    (hμ : ResU.Lower fρ μ) (hl : μ l = none)
    (k : ∀ x σ', ResU.CompS ρ (ResU.single l (CellU.ownOf v)) x → Cfg ls x ρf σ' ps →
      ResU.Lower σ' (BoCa.BoLo.Heap.upd μ l v) → WpAt ls (K.plug (.val (.loc l))) Q x ρf σ' ps) :
    WpAt ls (K.plug (.app (.val (.prim .alloc)) (.val v))) Q ρ ρf fρ ps := by
  obtain ⟨τ, hτ, hval⟩ := id hμ
  have hl' : τ.get l = none := (lower_eq_none_iff hval).mp hl
  have hρl : ρ.get l = none :=
    ((ResU.Comp.eq_none_iff hc.comp l).mp (get_eq_none_of_flat hτ hl')).2
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hρl)
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hc.comp hμ hl hx
  obtain ⟨y, hy, hyσ'⟩ := (ResU.CompS.assoc ρf ρ (ResU.single l (CellU.ownOf v)) σ').mp
    ⟨x, hx, hσ'x⟩
  cases ResU.CompS.functional hy hc.comp
  have hT' : TW σ' ps (rsOf ls) := TW.alloc hc.tw hμ hl hyσ' (hash_valid_comp hfx hσ'x)
  have htg' := tagged_of_ag (fun a ha => alloc_ag hyσ' ha) hc.tag
  obtain ⟨ρ', ρp, fρ', fρ'p, π, w, μ₁, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, h₁₅⟩ := k x σ' hx ⟨hfx, hσ'x, hT', htg'⟩ hlow'
  cases ResU.Lower.functional h₄ hlow'
  refine ⟨ρ', ρp, fρ', fρ'p, π, w, μ, μ', ps', ls', h₁, h₂, h₃, hμ, h₅, h₆, ?_, h₈,
    ResU.UpdV.trans (updV_compS_own hx (hash_valid hc.hash).2 (hash_valid hfx).2) h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, h₁₅⟩
  exact .more ⟨K, _, _, rfl, rfl, Head.alloc μ v l hl⟩ h₇

/-! ### Block allocation -/

/-- `(e↑)[s/0] = e`. -/
theorem subst_shift_one (e : Expr) (s : Val) : (e.shift 1 0).subst 0 s = e := by
  have := Expr.subst_shift 0 0 0 s e (le_refl _) (by omega)
  rw [Expr.shift_zero] at this
  exact this

/-- `v` has the pair structure of `σ`. -/
def ShapeV : Shape → Val → Prop
  | .leaf _, _ => True
  | .node s₁ s₂, v => ∃ v₁ v₂, v = .pair v₁ v₂ ∧ ShapeV s₁ v₁ ∧ ShapeV s₂ v₂

/-- The cells of the block at `b` holding the leaves of `v`: `b + i ↦ vᵢ`. -/
def Cells : Shape → Loc → Val → WRes → Prop
  | .leaf _, b, v, c => c = ResU.single b (CellU.ownOf v)
  | .node s₁ s₂, b, v, c => ∃ v₁ v₂ c₁ c₂, v = .pair v₁ v₂ ∧ ResU.CompS c₁ c₂ c ∧
      Cells s₁ b v₁ c₁ ∧ Cells s₂ (b + s₁.size) v₂ c₂

theorem shapeV_of_vP : ∀ {σ : Shape} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    vP σ.valTy ls δ v ρ → ShapeV σ v
  | .leaf _, _, _, _, _, _ => trivial
  | .node _ _, _, _, _, _, h => by
      obtain ⟨v₁, v₂, h⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, -, h₁, h₂⟩ := pure_sep_iff.mp h
      exact ⟨v₁, v₂, rfl, shapeV_of_vP h₁, shapeV_of_vP h₂⟩

/-- `allocS σ v` places the leaves at `b, b+1, …`, when every location from `b` on is free.
The continuation receives the block's cells and a configuration where every location from
`b + size σ` on is still free. -/
theorem wpAt_allocS {ls : List SRec} {Q : List SRec → Val → WProp} {ρf : WRes}
    {ps : List FrameRec} :
    ∀ (σ : Shape) (K : Kont) (b : Loc) {v : Val} {ρ fρ : WRes} {μ : Heap},
    Cfg ls ρ ρf fρ ps → ResU.Lower fρ μ → (∀ k, b ≤ k → μ k = none) → ShapeV σ v →
    (∀ x σ' c μ', ResU.CompS ρ c x → Cells σ b v c → Cfg ls x ρf σ' ps → ResU.Lower σ' μ' →
      (∀ k, b + σ.size ≤ k → μ' k = none) → WpAt ls (K.plug (σ.addr b).1) Q x ρf σ' ps) →
    WpAt ls (K.plug (.app (allocS σ) v.1)) Q ρ ρf fρ ps
  | .leaf _, K, b, v, ρ, fρ, μ, hc, hμ, hfree, _, k => by
      refine wpAt_alloc K v b hc hμ (hfree b (le_refl _)) fun x σ' hx hc' hlow => ?_
      refine k x σ' _ _ hx rfl hc' hlow fun j hj => ?_
      have hj' : b + 1 ≤ j := hj
      have hjb : j ≠ b := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hj')
      rw [BoCa.BoLo.Heap.upd_other hjb]
      exact hfree j (Nat.le_trans (Nat.le_succ b) hj')
  | .node s₁ s₂, K, b, v, ρ, fρ, μ, hc, hμ, hfree, hv, k => by
      obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := hv
      have ha₁ := allocS_closed s₁
      have ha₂ := allocS_closed s₂
      refine wpAt_pure (e' := K.plug (.letpair (Val.pair v₁ v₂).1
          (.pair (.app (allocS s₁) (.var 1)) (.app (allocS s₂) (.var 0))))) (fun μ => ?_) ?_
      · refine ⟨K, _, _, rfl, ?_, Head.beta μ _ (Val.pair v₁ v₂)⟩
        simp [Expr.subst, subst_closedAt _ _ ha₁, subst_closedAt _ _ ha₂]
      refine wpAt_pure (e' := K.plug (.pair (.app (allocS s₁) v₁.1) (.app (allocS s₂) v₂.1)))
        (fun μ => ?_) ?_
      · refine ⟨K, _, _, rfl, ?_, Head.letpair μ v₁ v₂ _⟩
        simp [Expr.subst, subst_closedAt _ _ ha₁, subst_closedAt _ _ ha₂, subst_shift_one]
      have e₁ : K.plug (.pair (.app (allocS s₁) v₁.1) (.app (allocS s₂) v₂.1)) =
          (K.comp (.pairL .hole (.app (allocS s₂) v₂.1))).plug (.app (allocS s₁) v₁.1) := by
        rw [Kont.plug_comp]; rfl
      rw [e₁]
      refine wpAt_allocS s₁ _ b hc hμ hfree hv₁ fun x₁ σ₁ c₁ μ₁ hx₁ hc₁ hcfg₁ hlow₁ hfree₁ => ?_
      have e₂ : (K.comp (.pairL .hole (.app (allocS s₂) v₂.1))).plug (s₁.addr b).1 =
          (K.comp (.pairR (s₁.addr b) .hole)).plug (.app (allocS s₂) v₂.1) := by
        rw [Kont.plug_comp, Kont.plug_comp]; rfl
      rw [e₂]
      refine wpAt_allocS s₂ _ (b + s₁.size) hcfg₁ hlow₁ hfree₁ hv₂
        fun x₂ σ₂ c₂ μ₂ hx₂ hc₂ hcfg₂ hlow₂ hfree₂ => ?_
      have e₃ : (K.comp (.pairR (s₁.addr b) .hole)).plug (s₂.addr (b + s₁.size)).1 =
          K.plug ((Shape.node s₁ s₂).addr b).1 := by
        rw [Kont.plug_comp]; rfl
      rw [e₃]
      obtain ⟨c, hc12, hxc⟩ := compS_reassoc hx₁ hx₂
      refine k x₂ σ₂ c μ₂ hxc ⟨v₁, v₂, c₁, c₂, rfl, hc12, hc₁, hc₂⟩ hcfg₂ hlow₂ fun j hj => ?_
      have hj' : b + (s₁.size + s₂.size) ≤ j := hj
      exact hfree₂ j (by rw [Nat.add_assoc]; exact hj')

/-- The block's cells and the values' resources make the family's resource. -/
theorem cells_refTy {ls : List SRec} {δ : LSub} :
    ∀ (σ : Shape) {b : Loc} {v : Val} {c ρ x : WRes}, Cells σ b v c → vP σ.valTy ls δ v ρ →
      ResU.CompS ρ c x → vP σ.refTy ls δ (σ.addr b) x
  | .leaf _, b, v, c, ρ, x, hc, hv, hx => by
      subst hc
      exact ⟨b, v, pure_sep_mk rfl ⟨_, ρ, ResU.CompS.comm hx, rfl, hv⟩⟩
  | .node s₁ s₂, b, v, c, ρ, x, hc, hv, hx => by
      obtain ⟨v₁, v₂, c₁, c₂, rfl, hc12, hcl₁, hcl₂⟩ := hc
      obtain ⟨w₁, w₂, hv⟩ := hv
      obtain ⟨hw, ρ₁, ρ₂, hρ12, hv₁, hv₂⟩ := pure_sep_iff.mp hv
      simp only [Val.pair, Subtype.mk.injEq, Expr.pair.injEq] at hw
      have e₁ : w₁ = v₁ := Subtype.ext hw.1.symm
      have e₂ : w₂ = v₂ := Subtype.ext hw.2.symm
      subst e₁ e₂
      obtain ⟨y, hy, hxy⟩ := compS_reassoc hρ12 hx
      obtain ⟨z, hz, hyz⟩ := compS_lcomm hc12 hy
      obtain ⟨u, hu, hxu⟩ := compS_reassoc' hyz hxy
      exact ⟨_, _, pure_sep_mk rfl ⟨u, z, hxu, cells_refTy s₁ hcl₁ hv₁ hu,
        cells_refTy s₂ hcl₂ hv₂ hz⟩⟩

/-- Some base has every location from it on free. -/
theorem exists_free_above (μ : Heap) (fρ : WRes) (hμ : ResU.Lower fρ μ) :
    ∃ b, ∀ k, b ≤ k → μ k = none := by
  obtain ⟨τ, -, hval⟩ := hμ
  obtain ⟨d, hd⟩ := τ.finite
  refine ⟨d.sum + 1, fun k hk => ?_⟩
  rw [hval k]
  by_cases h : τ.get k = none
  · rw [h]; rfl
  · have : k ≤ d.sum := List.le_sum_of_mem (hd k h)
    exact absurd hk (Nat.not_le.mpr (Nat.lt_succ_of_le this))

/-- **Block allocation.**  `allocS σ v` allocates the product as one block: there is a base
`b` with the returned handle `addr b σ`, packed. -/
theorem wpTS_allocS (σ : Shape) {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (hv : vP σ.valTy ls δ v ρ) :
    wpTS ls (.app (allocS σ) v.1) (fun ls' w => fun ρ' => ∃ b, Packed σ b ls' δ w ρ') ρ := by
  refine wpTS_of_wpAt fun ρf fρ ps hc => ?_
  obtain ⟨μ, hμ⟩ := lower_of_hash hc.hash hc.comp
  obtain ⟨b, hb⟩ := exists_free_above μ fρ hμ
  have := wpAt_allocS (Q := fun ls' w => fun ρ' => ∃ b, Packed σ b ls' δ w ρ') σ .hole b hc hμ hb
    (shapeV_of_vP hv) fun x σ' c μ' hx hcells hcfg _ _ =>
      wpAt_val hcfg ⟨b, rfl, cells_refTy σ hcells hv hx⟩
  simpa using this

end BoCa.Fig16.LogRel.Core

end
