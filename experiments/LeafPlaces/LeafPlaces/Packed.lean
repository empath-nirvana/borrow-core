import LeafPlaces.Typing
import LeafPlaces.Weaken
import LeafPlaces.Track

/-!
# The packed handle at the typed world

`Packed σ b` is the typed world's relation at `refTy σ`, restricted to the one handle a block
at base `b` has: `addr b σ`.  It is the semantic counterpart of a one-word struct handle.

* **Pack and unpack** (`packed_node`): a packed handle at a node is exactly a packed handle of
  each child, at the child's sub-block.  No resource changes hands and the value is the same
  tuple: the isomorphism is the identity.
* **Block allocation** (`wpTS_allocS`): `allocS σ v` has a run that places every leaf in one
  fresh block, at every frame the typed world admits.  `wpTS` chooses the run, and the machine
  lets `alloc` take any fresh location; the proof takes `b` above every allocated location and
  allocates `b, b+1, …` in order.
* **Borrowing keeps the handle packed** (`withborS_packed`): after `withborS σ` the handle it
  returns is the one it was given (`withborS_ret`), so it is packed at the same block.

`WpAt` is `wpTS`'s body at one fixed frame.  Block allocation needs it: the freshness of the
block's later leaves is a fact about the whole configuration, which a `wpTS` proof composed
from single allocations does not keep (each `wpTS` quantifies over its own frame).
-/

noncomputable section

namespace BoCa.LeafPlaces
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Typed
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ## The packed handle -/

/-- `𝒱⟦refTy σ⟧` at the handle of the block at `b`. -/
def Packed (σ : Shape) (b : Loc) (ls : List SRec) (δ : LSub) (v : Val) : WProp :=
  fun ρ => v = σ.addr b ∧ vP σ.refTy ls δ v ρ

/-- Unpack and pack: a packed node is a packed pair of children, at their sub-blocks. -/
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

/-- A packed handle is a handle of the family type (unpack forgets the block). -/
theorem packed_vP {σ : Shape} {b : Loc} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : Packed σ b ls δ v ρ) : vP σ.refTy ls δ v ρ := h.2

/-- A packed handle at a leaf is the leaf's own cell. -/
theorem packed_leaf {T : Ty} {b : Loc} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes} :
    Packed (.leaf T) b ls δ v ρ ↔ v = .loc b ∧ vP (.ref T) ls δ (.loc b) ρ := by
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩

/-! ## `wpTS` at one frame -/

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

/-- A value. -/
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

/-- `alloc v` at a chosen location `l` free in the whole configuration, under `K`: the
continuation receives the configuration with `l ↦ v` added to the run's resource. -/
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

/-! ## Block allocation -/

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
      -- `λv. let (v₁, v₂) = v; (allocS s₁ v₁, allocS s₂ v₂)` at `(v₁, v₂)`
      have ha₁ := clAt_allocS s₁
      have ha₂ := clAt_allocS s₂
      refine wpAt_pure (e' := K.plug (.letpair (Val.pair v₁ v₂).1
          (.pair (.app (allocS s₁) (.var 1)) (.app (allocS s₂) (.var 0))))) (fun μ => ?_) ?_
      · refine ⟨K, _, _, rfl, ?_, Head.beta μ _ (Val.pair v₁ v₂)⟩
        simp [Expr.subst, subst_clAt _ _ ha₁, subst_clAt _ _ ha₂]
      refine wpAt_pure (e' := K.plug (.pair (.app (allocS s₁) v₁.1) (.app (allocS s₂) v₂.1)))
        (fun μ => ?_) ?_
      · refine ⟨K, _, _, rfl, ?_, Head.letpair μ v₁ v₂ _⟩
        simp [Expr.subst, subst_clAt _ _ ha₁, subst_clAt _ _ ha₂]
      -- the first child's block, then the second's
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
      -- (ρ₁ ● ρ₂) ● (c₁ ● c₂) = (ρ₁ ● c₁) ● (ρ₂ ● c₂)
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

/-- **Block allocation.**  `allocS σ v` allocates the struct as one block: there is a base
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

/-! ## Borrowing keeps the handle packed -/

/-- A `wpTS` whose every run ends in a value satisfying `R` has `R` in its postcondition. -/
theorem wpTS_track {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ : WRes}
    (R : Val → Prop) (hR : ∀ μ μ' (w : Val), Steps μ e μ' w.1 → R w) (h : wpTS ls e Q ρ) :
    wpTS ls e (fun ls' w => fun ρ' => R w ∧ Q ls' w ρ') ρ := by
  intro ρf fρ ps hf hc hT htg
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, h₁₅⟩ := h ρf fρ ps hf hc hT htg
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, ⟨hR μ μ' v h₇, h₁₅⟩⟩

/-- A closing substitution of one value. -/
theorem substAll_one (s : Val) (e : Expr) : substAll [s] e = e.subst 0 s := by
  rw [substAll, Expr.psub_cons, Adequacy.psub_nil, Val.shift_zero]

/-- The context `x : refTy σ` at a packed handle. -/
theorem gDenX_packed {σ : Shape} {b : Loc} {ls : List SRec} {δ : LSub} {s : Val} {ρ : WRes}
    (hs : Packed σ b ls δ s ρ) : gDenX ls δ [⟨σ.refTy, true⟩] [s] ρ :=
  gDenX_mk trivial ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, hs.2, rfl, trivial⟩

/-- **Borrowing keeps the handle packed.**  `withborS σ s cb`, at a packed `s`, returns
`(s, t)`: the same handle, packed at the same block, and the callback's result.  `hd` is the
derivation of the call with the handle as its free variable (`withborS_wf` and `cb`'s
derivation); the Fundamental Property gives its `wpTS`, and `withborS_ret` the value. -/
theorem withborS_packed {Δ : LifeCtx} (hΔ : Δ.Ok) {σ : Shape} {cb : Expr} {T : Ty}
    (hcl : clAt 0 cb = true) (hcv : IsVal cb)
    (hd : DerivesWf Δ [⟨σ.refTy, true⟩] (Programs.app2 (withborS σ) (.var 0) cb)
      (.tensor σ.refTy T))
    (hsc : σ.refTy.scopedB Δ = true) {δ : LSub} (hδ : Δ.Models δ) {ls : List SRec} {b : Loc}
    {s : Val} {ρ : WRes} (hs : Packed σ b ls δ s ρ) :
    wpTS ls (Programs.app2 (withborS σ) s.1 cb)
      (fun ls' w => fun ρ' => ∃ t, w = .pair s t ∧ (Packed σ b ls' δ s ⋆ vP T ls' δ t) ρ') ρ := by
  have hsem := fundamentalProperty Δ _ _ _ hd hΔ (fun s' hs' _ => by
    simp only [List.mem_singleton] at hs'; subst hs'; exact hsc)
  have hw := hsem δ [s] ls ρ hδ (gDenX_packed hs)
  rw [substAll_one] at hw
  simp only [Programs.app2, Expr.subst, withborS_subst, subst_clAt _ _ hcl (Nat.zero_le 0)] at hw
  have hsa : clAt 0 s.1 = true := by rw [hs.1]; exact clAt_addr σ b
  have ht := wpTS_track (fun w => ∃ r, w = Val.pair s r) (fun μ μ' w hrun => by
    obtain ⟨r, hr, -⟩ := withborS_ret σ (g := ⟨cb, hcv⟩) hsa hcl hrun
    exact ⟨r, hr⟩) hw
  refine wpTS_mono (fun ls' w ρ' ⟨⟨r, hr⟩, hv⟩ => ?_) ρ ht
  subst hr
  obtain ⟨v₁, v₂, hv⟩ := hv
  obtain ⟨he, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hv
  simp only [Val.pair, Subtype.mk.injEq, Expr.pair.injEq] at he
  have e₁ : v₁ = s := Subtype.ext he.1.symm
  have e₂ : v₂ = r := Subtype.ext he.2.symm
  subst e₁ e₂
  exact ⟨v₂, rfl, ρ₁, ρ₂, hc, ⟨hs.1, h₁⟩, h₂⟩

/-- The call `withborS σ x cb` with `x : refTy σ` free, from the rule and a closed callback. -/
theorem d_call {Δ : LifeCtx} {σ : Shape} {cb : Expr} {C T : Ty}
    (hW : DerivesWf Δ [⟨σ.refTy, false⟩] (withborS σ) (.lolli σ.refTy (.lolli C (.tensor σ.refTy T))))
    (hcb : DerivesWf Δ [] cb C) :
    DerivesWf Δ [⟨σ.refTy, true⟩] (Programs.app2 (withborS σ) (.var 0) cb) (.tensor σ.refTy T) :=
  .lolliE (.right .nil) (DerivesWf.append_dead (Γ' := [⟨σ.refTy, false⟩]) (.cons .nil) hcb)
    (.lolliE (.left .nil) (.var (.here .nil)) hW)

/-- **Allocate a struct as one block, then borrow its leaves.**  The handle that comes back is
the block's: `(addr b σ, t)`, packed at `b`. -/
theorem wpTS_allocBorrow {Δ : LifeCtx} (hΔ : Δ.Ok) {σ : Shape} {v cb : Val} {T : Ty}
    (hcl : clAt 0 cb.1 = true)
    (hd : DerivesWf Δ [⟨σ.refTy, true⟩] (Programs.app2 (withborS σ) (.var 0) cb.1)
      (.tensor σ.refTy T))
    (hsc : σ.refTy.scopedB Δ = true) {δ : LSub} (hδ : Δ.Models δ) {ls : List SRec} {ρ : WRes}
    (hv : vP σ.valTy ls δ v ρ) :
    wpTS ls (Programs.app2 (withborS σ) (.app (allocS σ) v.1) cb.1)
      (fun ls' w => fun ρ' => ∃ b t, w = .pair (σ.addr b) t ∧
        (Packed σ b ls' δ (σ.addr b) ⋆ vP T ls' δ t) ρ') ρ := by
  have hb := wpTS_bind (.appL (.appR (withborS σ) .hole) cb) (.app (allocS σ) v.1) ls
    (fun ls' w => fun ρ' => ∃ b t, w = .pair (σ.addr b) t ∧
        (Packed σ b ls' δ (σ.addr b) ⋆ vP T ls' δ t) ρ')
  refine hb ρ (wpTS_mono (fun ls' w ρ' ⟨b, hp⟩ => ?_) ρ (wpTS_allocS σ hv))
  have hw := withborS_packed hΔ hcl cb.2 hd hsc hδ hp
  refine wpTS_mono (fun ls'' u ρ'' ⟨t, hu, ht⟩ => ⟨b, t, ?_, ?_⟩) ρ' hw
  · rw [hu, hp.1]
  · rw [← hp.1]; exact ht

end BoCa.LeafPlaces

end
