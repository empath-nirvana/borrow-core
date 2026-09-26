import Optics.Traversal

/-!
# Optics — the shape law of IterMut, on every run  (stage 3)

`ListAt μ v ns`: the list value `v` sits in the heap `μ` with node cells `ns`, each node a value
cell `a` and a next cell `b` (the common list, `CommonList.lean`).  The cells are distinct
(`Cells.Nodup`).

**Shape law** (`iterMut_shape`): on every run of `iterMut v g` to a value, the result is
`(v, ())` — the same root —, the list sits at the same node cells, every next cell holds what
it held, and only the value cells may have changed; so the length is preserved.  The callback
is assumed to act only on the cell it is lent (`ElemFrame`): typing gives this through the
borrow, and the bare machine does not, so it is a hypothesis of the law.

The proof steps through `foldReuse`'s recursion by induction on the nodes, with the machine's
runs characterised by the equations of `Runs.lean`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Optics
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Kont)
open BoCa.Programs (app2 alloc' free' unitNoLeak)

attribute [local simp] Expr.subst Expr.shift Val.val_shift Expr.shift_zero

/-! ### More run equations -/

/-- `u; e` at a value runs only at `()`. -/
theorem steps_seq_val_iff {μ μ' : Heap} {u w : Val} {e : Expr} :
    Steps μ (.seq u.1 e) μ' w.1 ↔ u = .unit ∧ Steps μ e μ' w.1 := by
  constructor
  · intro h
    generalize hE : Expr.seq u.1 e = E at h
    cases h with
    | refl => exact absurd (hE ▸ w.2) (by simp)
    | more hs t =>
        subst hE
        have hh := step1_top hs fun K c hE hK => by
          cases K with
          | hole => exact absurd rfl hK
          | seq K u' =>
              simp only [Kont.plug, Expr.seq.injEq] at hE
              exact K.isVal_of_plug (hE.1 ▸ u.2)
          | _ => simp [Kont.plug] at hE
        generalize hE' : Expr.seq u.1 e = E at hh
        cases hh with
        | seq _ =>
            simp only [Expr.seq.injEq] at hE'
            obtain ⟨hu, rfl⟩ := hE'
            exact ⟨Subtype.ext hu, t⟩
        | _ => simp at hE'
  · rintro ⟨rfl, h⟩
    exact steps_seq_iff.mpr h

/-- `swap b v` at a cell: returns `(b, t)` for the old content `t` and stores `v`. -/
theorem steps_swap_iff {μ μ' : Heap} {b : Loc} {v w : Val} :
    Steps μ (app2 swap (Val.loc b).1 v.1) μ' w.1 ↔
      ∃ t : Val, μ b = some t ∧ μ' = μ.upd b v ∧ w = .pair (.loc b) t := by
  rw [show swap = lam2 (elet (.app load' v1) (.seq (.app (.app store' v2) v1) (.pair v2 v0)))
    from rfl, steps_app2_iff]
  have e : ((elet (.app load' v1) (.seq (.app (.app store' v2) v1) (.pair v2 v0))).subst 1
      ((Val.loc b).shift 1 0)).subst 0 v
      = .app (.val (Val.lam (.seq (.app (.app store' (Val.loc b).1) (v.shift 1 0).1)
          (.pair (Val.loc b).1 (.var 0))))) (.app load' (Val.loc b).1) := by
    simp [elet, v0, v1, v2, load', store']
  rw [e, steps_appR_iff]
  constructor
  · rintro ⟨μm, t, hl, h⟩
    obtain ⟨hb, rfl⟩ := steps_load_iff.mp hl
    rw [steps_beta_iff] at h
    have e₂ : (Expr.seq (.app (.app store' (Val.loc b).1) (v.shift 1 0).1)
        (.pair (Val.loc b).1 (.var 0))).subst 0 t
        = .seq (.app (.app store' (Val.loc b).1) v.1) (Val.pair (.loc b) t).1 := by
      simp [store', Expr.subst_shift 0 0 0 t v.1 (le_refl _) (le_refl _)]
    rw [e₂, steps_seqK_iff] at h
    obtain ⟨μs, u, hst, hrest⟩ := h
    obtain ⟨-, rfl, rfl⟩ := steps_store_iff.mp hst
    obtain ⟨rfl, rfl⟩ := steps_val_iff.mp (steps_seq_iff.mp hrest)
    exact ⟨t, hb, rfl, rfl⟩
  · rintro ⟨t, hb, rfl, rfl⟩
    refine ⟨μ, t, steps_load_iff.mpr ⟨hb, rfl⟩, ?_⟩
    rw [steps_beta_iff]
    have e₂ : (Expr.seq (.app (.app store' (Val.loc b).1) (v.shift 1 0).1)
        (.pair (Val.loc b).1 (.var 0))).subst 0 t
        = .seq (.app (.app store' (Val.loc b).1) v.1) (Val.pair (.loc b) t).1 := by
      simp [store', Expr.subst_shift 0 0 0 t v.1 (le_refl _) (le_refl _)]
    rw [e₂, steps_seqK_iff]
    exact ⟨_, .unit, steps_store_iff.mpr ⟨⟨t, hb⟩, rfl, rfl⟩, steps_seq_iff.mpr (.refl _ _)⟩

/-- `fill (b, r)`: stores `r` in the emptied cell `b` and returns `b`. -/
theorem steps_fill_iff {μ μ' : Heap} {b : Loc} {r w : Val} :
    Steps μ (.app (.val fillV) (Val.pair (.loc b) r).1) μ' w.1 ↔
      μ b = some .unit ∧ μ' = μ.upd b r ∧ w = .loc b := by
  rw [show Expr.val fillV = .val (Val.lam fillB) from rfl, steps_beta_iff]
  have e : fillB.subst 0 (Val.pair (.loc b) r)
      = .letpair (Val.pair (.loc b) r).1 (bindE (.app (.app swap (.var 1)) (.var 0))
          (.letpair (.var 0) (.seq (.var 0) (.var 1)))) := by
    simp [fillB, bindE, swap_subst]
  rw [e, steps_letpair_iff]
  have e₂ : ((bindE (.app (.app swap (.var 1)) (.var 0))
      (.letpair (.var 0) (.seq (.var 0) (.var 1)))).subst 0 (r.shift 1 0)).subst 0 (Val.loc b)
      = .app (.val (Val.lam (.letpair (.var 0) (.seq (.var 0) (.var 1)))))
          (app2 swap (Val.loc b).1 r.1) := by
    simp [bindE, app2, swap_subst, Expr.subst_shift 0 0 0 (Val.loc b) r.1 (le_refl _) (le_refl _)]
  rw [e₂, steps_appR_iff]
  constructor
  · rintro ⟨μm, p, hs, h⟩
    obtain ⟨t, hb, rfl, rfl⟩ := steps_swap_iff.mp hs
    rw [steps_beta_iff] at h
    have e₃ : (Expr.letpair (.var 0) (.seq (.var 0) (.var 1))).subst 0 (Val.pair (.loc b) t)
        = .letpair (Val.pair (.loc b) t).1 (.seq (.var 0) (.var 1)) := by simp
    rw [e₃, steps_letpair_iff] at h
    have e₄ : ((Expr.seq (.var 0) (.var 1)).subst 0 (t.shift 1 0)).subst 0 (Val.loc b)
        = .seq t.1 (Val.loc b).1 := by
      simp [Expr.subst_shift 0 0 0 (Val.loc b) t.1 (le_refl _) (le_refl _)]
    rw [e₄, steps_seq_val_iff] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := steps_val_iff.mp h
    exact ⟨hb, rfl, rfl⟩
  · rintro ⟨hb, rfl, rfl⟩
    refine ⟨_, _, steps_swap_iff.mpr ⟨.unit, hb, rfl, rfl⟩, ?_⟩
    rw [steps_beta_iff]
    have e₃ : (Expr.letpair (.var 0) (.seq (.var 0) (.var 1))).subst 0 (Val.pair (.loc b) .unit)
        = .letpair (Val.pair (.loc b) .unit).1 (.seq (.var 0) (.var 1)) := by simp
    rw [e₃, steps_letpair_iff]
    have e₄ : ((Expr.seq (.var 0) (.var 1)).subst 0 (Val.unit.shift 1 0)).subst 0 (Val.loc b)
        = .seq Val.unit.1 (Val.loc b).1 := by simp
    rw [e₄, steps_seq_val_iff]
    exact ⟨rfl, .refl _ _⟩

/-! ### `foldReuse`'s recursion, as runs -/

/-- **Unrolling**: `selfV B g` runs as `fixV B g`. -/
theorem steps_selfV_iff {B : Expr} (hB : closedAt 2 B = true) {μ μ' : Heap} {g r : Val} :
    Steps μ (.app (.val (selfV B)) g.1) μ' r.1 ↔ Steps μ (.app (.val (fixV B)) g.1) μ' r.1 := by
  have hX := zX_closed hB
  rw [show Expr.val (selfV B) = .val (Val.lam (.app (.app (.val (zX B)) (.val (zX B))) (.var 0)))
    from rfl, steps_beta_iff]
  have h₁ : (Expr.app (.app (.val (zX B)) (.val (zX B))) (.var 0)).subst 0 g
      = .app (.app (.val (zX B)) (.val (zX B))) g.1 := by
    simp only [Expr.subst, val_subst_closed hX]; rfl
  rw [h₁, steps_appL_iff]
  have h₂ : (Expr.app (.val (.lam (.lam B)))
      (.val (.lam (.app (.app (.var 1) (.var 1)) (.var 0))))).subst 0 (zX B)
      = .app (.val (Val.lam (.lam B))) (.val (selfV B)) := by
    simp [selfV, Expr.subst, val_shift_closed hX, subst_closedAt B (k := 2) (j := 2) _ hB le_rfl]
  have hxx : ∀ {μ₁ : Heap} {u : Val}, Steps μ (.app (.val (zX B)) (.val (zX B))) μ₁ u.1 ↔
      μ₁ = μ ∧ u = fixV B := fun {μ₁ u} => by
    show Steps μ (.app (.val (Val.lam (.app (.val (Val.lam (.lam B)))
      (.val (Val.lam (.app (.app (.var 1) (.var 1)) (.var 0))))))) (zX B).1) μ₁ u.1 ↔ _
    rw [steps_beta_iff, h₂, steps_beta_iff]
    have h₃ : (Expr.lam B).subst 0 (selfV B) = (fixV B).1 := by simp [fixV, Expr.subst]
    rw [h₃]
    exact steps_val_iff
  constructor
  · rintro ⟨μm, u, h, h'⟩
    obtain ⟨rfl, rfl⟩ := hxx.mp h
    exact h'
  · intro h
    exact ⟨μ, fixV B, hxx.mpr ⟨rfl, rfl⟩, h⟩

/-- **The recursive call**: `h w`, for `h = λw. self g w`, runs as `travR F h w to r. g r`. -/
theorem steps_hR_iff (F : FShape) {g : Val} {μ μ' : Heap} {w r : Val} :
    Steps μ (.app (.val (hR F g)) w.1) μ' r.1 ↔
      Steps μ (.app (.val (Val.lam (.app (.val (g.shift 1 0)) (.var 0))))
        (.app (.app (.val (travR F)) (.val (hR F g))) w.1)) μ' r.1 := by
  have hS := selfR_closed F
  rw [show Expr.val (hR F g) = .val (Val.lam (.app (.app (.val (selfR F)) (.val (g.shift 1 0)))
    (.var 0))) from rfl, steps_beta_iff]
  have e₁ : Expr.subst 0 w (.app (.app (.val (selfR F)) (.val (g.shift 1 0))) (.var 0))
      = .app (.app (.val (selfR F)) (.val g)) (.val w) := by
    simp [closed_subst hS, subst_shift_succ]
  rw [e₁, steps_appL_iff]
  have e₂ : ((fBR F).subst 1 (selfR F)).subst 0 g
      = (Val.lam (bindE (.app (.app (.val (travR F))
          (.val (.lam (.app (.app (.val (selfR F)) (.val (g.shift 2 0))) (.var 0))))) (.var 0))
          (.app (.val (g.shift 2 0)) (.var 0)))).1 := by
    simp [fBR, bindE, closed_subst (travR_closed _), closed_subst hS, closed_shift hS,
      Expr.shift_shift]
  have hsg : ∀ {μ₁ : Heap} {u : Val}, Steps μ (.app (.val (selfR F)) g.1) μ₁ u.1 ↔
      μ₁ = μ ∧ u = Val.lam (bindE (.app (.app (.val (travR F))
          (.val (.lam (.app (.app (.val (selfR F)) (.val (g.shift 2 0))) (.var 0))))) (.var 0))
          (.app (.val (g.shift 2 0)) (.var 0))) := fun {μ₁ u} => by
    rw [steps_selfV_iff (fBR_closed F), fixV_eq (fBR_closed F), steps_beta_iff, e₂]
    exact steps_val_iff
  constructor
  · rintro ⟨μm, u, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := hsg.mp h₁
    rw [steps_beta_iff, fBR_body F hS] at h₂
    exact h₂
  · intro h
    refine ⟨μ, _, hsg.mpr ⟨rfl, rfl⟩, ?_⟩
    rw [steps_beta_iff, fBR_body F hS]
    exact h

/-- `travR G h w` runs as its body. -/
theorem steps_travR_iff (G : FShape) {μ μ' : Heap} {h w r : Val} :
    Steps μ (.app (.app (.val (travR G)) h.1) w.1) μ' r.1 ↔
      Steps μ (((tR G).subst 1 (h.shift 1 0)).subst 0 w) μ' r.1 := by
  rw [travR_eq]
  exact steps_app2_iff

/-- At a leaf, `travR` returns its argument. -/
theorem steps_travR_leaf_iff {A : VTy} {μ μ' : Heap} {h w r : Val} :
    Steps μ (.app (.app (.val (travR (.leaf A))) h.1) w.1) μ' r.1 ↔ μ' = μ ∧ r = w := by
  rw [steps_travR_iff, tR_leaf]
  exact steps_val_iff

/-- At `Ref X`: the cell is emptied, the recursive call runs on its content, and the emptied
cell comes back with the result. -/
theorem steps_travR_refX_iff {μ μ' : Heap} {h r : Val} {b : Loc} :
    Steps μ (.app (.app (.val (travR .refX)) h.1) (Val.loc b).1) μ' r.1 ↔
      ∃ (t r' : Val), μ b = some t ∧ Steps (μ.upd b .unit) (.app h.1 t.1) μ' r'.1 ∧
        r = .pair (.loc b) r' := by
  rw [steps_travR_iff, tR_refX, Kont.plug, Kont.plug, steps_appR_iff]
  have e : ∀ t : Val, (Expr.letpair (.var 0) (bindE (.app (.val (h.shift 3 0)) (.var 0))
      (.pair (.var 2) (.var 0)))).subst 0 (Val.pair (.loc b) t)
      = .letpair (Val.pair (.loc b) t).1 ((bindE (.app (.val (h.shift 3 0)) (.var 0))
          (.pair (.var 2) (.var 0))).subst 2 ((Val.pair (.loc b) t).shift 2 0)) := fun t => rfl
  have e₂ : ∀ r' : Val, (Expr.pair (.val (Val.loc b)) (.var 0)).subst 0 r'
      = (Val.pair (.loc b) r').1 := fun r' => by simp
  constructor
  · rintro ⟨μm, p, hs, h₂⟩
    obtain ⟨t, hb, rfl, rfl⟩ := steps_swap_iff.mp hs
    rw [steps_beta_iff, e, steps_letpair_iff, refR_body, Kont.plug, Kont.plug,
      steps_appR_iff] at h₂
    obtain ⟨μn, r', hh, h₃⟩ := h₂
    rw [steps_beta_iff, e₂] at h₃
    obtain ⟨rfl, rfl⟩ := steps_val_iff.mp h₃
    exact ⟨t, r', hb, hh, rfl⟩
  · rintro ⟨t, r', hb, hh, rfl⟩
    refine ⟨_, _, steps_swap_iff.mpr ⟨t, hb, rfl, rfl⟩, ?_⟩
    rw [steps_beta_iff, e, steps_letpair_iff, refR_body, Kont.plug, Kont.plug, steps_appR_iff]
    refine ⟨μ', r', hh, ?_⟩
    rw [steps_beta_iff, e₂]
    exact .refl _ _

/-- The list's node shape. -/
abbrev nodeF (E : VTy) : FShape := .tensor (.leaf (.ref E)) .refX

/-- At a node `(a, b)`: the value cell is passed through, the next cell traversed. -/
theorem steps_travR_node_iff {E : VTy} {μ μ' : Heap} {h r : Val} {a b : Loc} :
    Steps μ (.app (.app (.val (travR (nodeF E))) h.1) (Val.pair (.loc a) (.loc b)).1) μ' r.1 ↔
      ∃ (t r' : Val), μ b = some t ∧ Steps (μ.upd b .unit) (.app h.1 t.1) μ' r'.1 ∧
        r = .pair (.loc a) (.pair (.loc b) r') := by
  rw [steps_travR_iff, tR_tensor, steps_letpair_iff, tensorR_body, Kont.plug, Kont.plug,
    steps_appR_iff]
  constructor
  · rintro ⟨μm, x, hx, h₂⟩
    obtain ⟨rfl, rfl⟩ := steps_travR_leaf_iff.mp hx
    rw [steps_beta_iff, tensorR_body₂, Kont.plug, Kont.plug, steps_appR_iff] at h₂
    obtain ⟨μn, y, hy, h₃⟩ := h₂
    obtain ⟨t, r', hb, hh, rfl⟩ := steps_travR_refX_iff.mp hy
    rw [steps_beta_iff] at h₃
    have e : (Expr.pair (.val ((Val.loc a).shift 1 0)) (.var 0)).subst 0 (Val.pair (.loc b) r')
        = (Val.pair (.loc a) (.pair (.loc b) r')).1 := by simp
    rw [e] at h₃
    obtain ⟨rfl, rfl⟩ := steps_val_iff.mp h₃
    exact ⟨t, r', hb, hh, rfl⟩
  · rintro ⟨t, r', hb, hh, rfl⟩
    refine ⟨μ, Val.loc a, steps_travR_leaf_iff.mpr ⟨rfl, rfl⟩, ?_⟩
    rw [steps_beta_iff, tensorR_body₂, Kont.plug, Kont.plug, steps_appR_iff]
    refine ⟨μ', .pair (.loc b) r', steps_travR_refX_iff.mpr ⟨t, r', hb, hh, rfl⟩, ?_⟩
    rw [steps_beta_iff]
    have e : (Expr.pair (.val ((Val.loc a).shift 1 0)) (.var 0)).subst 0 (Val.pair (.loc b) r')
        = (Val.pair (.loc a) (.pair (.loc b) r')).1 := by simp
    rw [e]
    exact .refl _ _

/-- The list's shape. -/
abbrev listF (E : VTy) : FShape := clistFE E

/-- At the empty list, `travR` returns it. -/
theorem steps_travR_nil_iff {E : VTy} {μ μ' : Heap} {h u r : Val} :
    Steps μ (.app (.app (.val (travR (listF E))) h.1) (Val.inj₁ u).1) μ' r.1 ↔
      μ' = μ ∧ r = .inj₁ u := by
  rw [steps_travR_iff, tR_sum, steps_case₁_iff, sumR_branch _ _ _ Expr.inj₁ (fun _ _ _ => rfl),
    Kont.plug, Kont.plug, steps_appR_iff]
  constructor
  · rintro ⟨μm, x, hx, h₂⟩
    obtain ⟨rfl, rfl⟩ := steps_travR_leaf_iff.mp hx
    rw [steps_beta_iff] at h₂
    exact steps_val_iff (v := Val.inj₁ x) |>.mp h₂
  · rintro ⟨rfl, rfl⟩
    refine ⟨μ', u, steps_travR_leaf_iff.mpr ⟨rfl, rfl⟩, ?_⟩
    rw [steps_beta_iff]
    exact .refl _ _

/-- At a node, `travR` traverses it and tags the result. -/
theorem steps_travR_cons_iff {E : VTy} {μ μ' : Heap} {h p r : Val} :
    Steps μ (.app (.app (.val (travR (listF E))) h.1) (Val.inj₂ p).1) μ' r.1 ↔
      ∃ r' : Val, Steps μ (.app (.app (.val (travR (nodeF E))) h.1) p.1) μ' r'.1 ∧ r = .inj₂ r' := by
  rw [steps_travR_iff, tR_sum, steps_case₂_iff, sumR_branch _ _ _ Expr.inj₂ (fun _ _ _ => rfl),
    Kont.plug, Kont.plug, steps_appR_iff]
  constructor
  · rintro ⟨μm, x, hx, h₂⟩
    rw [steps_beta_iff] at h₂
    obtain ⟨rfl, rfl⟩ := steps_val_iff (v := Val.inj₂ x) |>.mp h₂
    exact ⟨x, hx, rfl⟩
  · rintro ⟨r', hr, rfl⟩
    refine ⟨μ', r', hr, ?_⟩
    rw [steps_beta_iff]
    exact .refl _ _

/-! ### IterMut's algebra -/

/-- The algebra's body with the callback `g` substituted. -/
def itAlgG (g : Val) : Expr :=
  .case (.var 0) (.inj₁ (.var 0))
    (.letpair (.var 0)
      (.letpair (app2 (.val withborV) (.var 1) g.1)
        (.seq (.var 0) (.inj₂ (.pair (.var 1) (.app (.val fillV) (.var 2)))))))

def algG (g : Val) : Val := .lam (itAlgG g)

theorem algG_closed {g : Val} (hg : closedAt 0 g.1 = true) : closedAt 0 (algG g).1 = true := by
  simp [algG, itAlgG, app2, closedAt, withborV, fillV, fillB, bindE, swap, lam2, elet, v0, v1,
    v2, load', store', unit', closedAt_mono _ hg (Nat.zero_le _)]

/-- At the empty list the algebra returns it. -/
theorem steps_alg_nil_iff {g u r : Val} (hg : closedAt 0 g.1 = true) {μ μ' : Heap} :
    Steps μ (.app (.val (algG g)) (Val.inj₁ u).1) μ' r.1 ↔ μ' = μ ∧ r = .inj₁ u := by
  rw [show Expr.val (algG g) = .val (Val.lam (itAlgG g)) from rfl, steps_beta_iff]
  have e : (itAlgG g).subst 0 (Val.inj₁ u) = .case (Val.inj₁ u).1 (.inj₁ (.var 0))
      ((Expr.letpair (.var 0) (.letpair (app2 (.val withborV) (.var 1) g.1)
        (.seq (.var 0) (.inj₂ (.pair (.var 1) (.app (.val fillV) (.var 2))))))).subst 1
          ((Val.inj₁ u).shift 1 0)) := by
    simp [itAlgG, app2, closed_subst hg]
  rw [e, steps_case₁_iff]
  simp only [Expr.subst, if_true]
  exact steps_val_iff (v := Val.inj₁ u)

/-- At a node `(a, (b, r))`: the value cell `a` is lent to `g`, and the emptied next cell `b`
is refilled with `r`. -/
theorem steps_alg_cons_iff {g r' w : Val} (hg : closedAt 0 g.1 = true)
    (hr : closedAt 0 r'.1 = true) {a b : Loc} {μ μ' : Heap} :
    Steps μ (.app (.val (algG g)) (Val.inj₂ (.pair (.loc a) (.pair (.loc b) r'))).1) μ' w.1 ↔
      ∃ μ₁ : Heap, Steps μ (app2 g.1 unit' (Val.loc a).1) μ₁ Val.unit.1 ∧
        μ₁ b = some .unit ∧ μ' = μ₁.upd b r' ∧ w = .inj₂ (.pair (.loc a) (.loc b)) := by
  rw [show Expr.val (algG g) = .val (Val.lam (itAlgG g)) from rfl, steps_beta_iff]
  set P : Val := .pair (.loc a) (.pair (.loc b) r')
  have e : (itAlgG g).subst 0 (Val.inj₂ P) = .case (Val.inj₂ P).1 (.inj₁ (.var 0))
      ((Expr.letpair (.var 0) (.letpair (app2 (.val withborV) (.var 1) g.1)
        (.seq (.var 0) (.inj₂ (.pair (.var 1) (.app (.val fillV) (.var 2))))))).subst 1
          ((Val.inj₂ P).shift 1 0)) := by
    simp [itAlgG, app2, closed_subst hg]
  rw [e, steps_case₂_iff]
  have e₂ : ((Expr.letpair (.var 0) (.letpair (app2 (.val withborV) (.var 1) g.1)
      (.seq (.var 0) (.inj₂ (.pair (.var 1) (.app (.val fillV) (.var 2))))))).subst 1
        ((Val.inj₂ P).shift 1 0)).subst 0 P
      = .letpair P.1 (.letpair (app2 (.val withborV) (.var 1) g.1)
          (.seq (.var 0) (.inj₂ (.pair (.var 1) (.app (.val fillV) (.var 2)))))) := by
    simp [app2, withborV, fillV, fillB, bindE, swap, lam2, elet, v0, v1, v2, load', store', unit',
      closed_subst hg, closed_shift hg]
  rw [e₂, steps_letpair_iff]
  have e₃ : ((Expr.letpair (app2 (.val withborV) (.var 1) g.1)
      (.seq (.var 0) (.inj₂ (.pair (.var 1) (.app (.val fillV) (.var 2)))))).subst 0
        ((Val.pair (.loc b) r').shift 1 0)).subst 0 (Val.loc a)
      = .letpair (app2 (.val withborV) (Val.loc a).1 g.1)
          (.seq (.var 0) (.inj₂ (.pair (.var 1) (.app (.val fillV) (Val.pair (.loc b) r').1)))) := by
    simp [app2, withborV, fillV, fillB, bindE, swap, lam2, elet, v0, v1, v2, load', store', unit',
      closed_subst hg, closed_shift hr, closed_subst hr]
  rw [e₃, steps_letpairK_iff]
  have e₄ : ∀ u : Val, ((Expr.seq (.var 0) (.inj₂ (.pair (.var 1)
      (.app (.val fillV) (Val.pair (.loc b) r').1)))).subst 0 (u.shift 1 0)).subst 0 (Val.loc a)
      = .seq u.1 (.inj₂ (.pair (Val.loc a).1 (.app (.val fillV) (Val.pair (.loc b) r').1))) :=
    fun u => by
      simp [fillV, fillB, bindE, swap, lam2, elet, v0, v1, v2, load', store',
        Expr.subst_shift 0 0 0 (Val.loc a) u.1 (le_refl _) (le_refl _), closed_shift hr,
        closed_subst hr]
  constructor
  · rintro ⟨μm, v, h₁, h₂⟩
    obtain ⟨u, rfl, hgu⟩ := steps_withbor_iff.mp h₁
    rw [steps_letpair_iff, e₄, steps_seq_val_iff] at h₂
    obtain ⟨rfl, h₃⟩ := h₂
    obtain ⟨x, rfl, h₄⟩ := steps_inj₂_iff.mp h₃
    obtain ⟨y, rfl, h₅⟩ := steps_pairR_iff.mp h₄
    obtain ⟨hb, rfl, rfl⟩ := steps_fill_iff.mp h₅
    exact ⟨μm, hgu, hb, rfl, rfl⟩
  · rintro ⟨μ₁, hgu, hb, rfl, rfl⟩
    refine ⟨μ₁, .pair (.loc a) .unit, steps_withbor_iff.mpr ⟨.unit, rfl, hgu⟩, ?_⟩
    rw [steps_letpair_iff, e₄, steps_seq_val_iff]
    refine ⟨rfl, steps_inj₂_iff.mpr ⟨_, rfl, steps_pairR_iff.mpr ⟨_, rfl, ?_⟩⟩⟩
    exact steps_fill_iff.mpr ⟨hb, rfl, rfl⟩

/-! ### The shape law -/

/-- The list `v` sits in `μ` with nodes `ns`: each node a value cell `a` and a next cell `b`
holding the tail. -/
def ListAt (μ : Heap) : Val → List (Loc × Loc) → Prop
  | v, [] => v = .inj₁ .unit
  | v, (a, b) :: ns => v = .inj₂ (.pair (.loc a) (.loc b)) ∧ (∃ x, μ a = some x) ∧
      ∃ t, μ b = some t ∧ ListAt μ t ns

/-- The nodes' cells. -/
def cells : List (Loc × Loc) → List Loc
  | [] => []
  | (a, b) :: ns => a :: b :: cells ns

theorem mem_cells_of_fst {ns : List (Loc × Loc)} {k : Loc} (h : k ∈ ns.map Prod.fst) :
    k ∈ cells ns := by
  induction ns with
  | nil => simp at h
  | cons p ns ih =>
      obtain ⟨a, b⟩ := p
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp [cells]
      · simp [cells, ih h]

/-- `ListAt` depends only on the nodes' cells. -/
theorem ListAt.congr {μ μ' : Heap} : ∀ {v : Val} {ns : List (Loc × Loc)}, ListAt μ v ns →
    (∀ k ∈ cells ns, μ' k = μ k) → ListAt μ' v ns
  | _, [], h, _ => h
  | _, (a, b) :: ns, ⟨hv, ⟨x, ha⟩, t, hb, ht⟩, hk => by
      have ha' : μ' a = some x := by rw [hk a (by simp [cells]), ha]
      have hb' : μ' b = some t := by rw [hk b (by simp [cells]), hb]
      exact ⟨hv, ⟨x, ha'⟩, t, hb', ht.congr fun k hkm => hk k (by simp [cells, hkm])⟩

/-- The callback acts only on the cell it is lent: it keeps the heap closed, the cell defined,
and every other cell as it was. -/
def ElemFrame (g : Val) : Prop :=
  ∀ {μ μ' : Heap} {a : Loc} {t : Val}, HeapClosed μ → (∃ x, μ a = some x) →
    Steps μ (app2 g.1 unit' (Val.loc a).1) μ' t.1 →
      HeapClosed μ' ∧ (∃ x, μ' a = some x) ∧ ∀ k, k ≠ a → μ' k = μ k

theorem HeapClosed.upd {μ : Heap} {ℓ : Loc} {v : Val} (hμ : HeapClosed μ)
    (hv : closedAt 0 v.1 = true) : HeapClosed (μ.upd ℓ v) := by
  intro k u hk
  simp only [BoLo.Heap.upd] at hk
  split_ifs at hk
  · cases hk; exact hv
  · exact hμ k u hk

/-- **The recursive call preserves the shape**: `foldReuse`'s recursion with IterMut's algebra
returns its argument, keeps the list at its cells, and changes only value cells. -/
theorem fold_shape {g : Val} (hg : closedAt 0 g.1 = true) (hfr : ElemFrame g) {E : VTy} :
    ∀ (ns : List (Loc × Loc)) {μ μ' : Heap} {v w : Val}, HeapClosed μ → ListAt μ v ns →
      (cells ns).Nodup →
      Steps μ (.app (.val (hR (listF E) (algG g))) v.1) μ' w.1 →
      w = v ∧ ListAt μ' v ns ∧ HeapClosed μ' ∧ ∀ k, k ∉ ns.map Prod.fst → μ' k = μ k
  | [], μ, μ', v, w, hμ, hv, _, h => by
      obtain rfl : v = .inj₁ .unit := hv
      rw [steps_hR_iff, steps_appR_iff] at h
      obtain ⟨μm, r, hr, h₂⟩ := h
      obtain ⟨rfl, rfl⟩ := steps_travR_nil_iff.mp hr
      rw [steps_beta_iff, algR_subst] at h₂
      obtain ⟨rfl, rfl⟩ := (steps_alg_nil_iff hg).mp h₂
      exact ⟨rfl, rfl, hμ, fun _ _ => rfl⟩
  | (a, b) :: ns, μ, μ', v, w, hμ, hv, hnd, h => by
      obtain ⟨rfl, ⟨x, ha⟩, t, hb, ht⟩ := hv
      have hnd' : (cells ns).Nodup := hnd.sublist (by simp [cells])
      have ha_ns : a ∉ cells ns := by simp [cells] at hnd; exact hnd.1.2
      have hb_ns : b ∉ cells ns := by simp [cells] at hnd; exact hnd.2.1
      have hab : a ≠ b := by simp [cells] at hnd; exact hnd.1.1
      have htc : closedAt 0 t.1 = true := hμ b t hb
      rw [steps_hR_iff, steps_appR_iff] at h
      obtain ⟨μ₂, r, hr, h₂⟩ := h
      obtain ⟨r₁, hr₁, rfl⟩ := steps_travR_cons_iff.mp hr
      obtain ⟨t', r', hb', hrec, rfl⟩ := steps_travR_node_iff.mp hr₁
      obtain rfl : t' = t := Option.some.inj (hb'.symm.trans hb)
      -- the tail, from the heap with `b` emptied
      have hμb : HeapClosed (μ.upd b .unit) := hμ.upd rfl
      have htl : ListAt (μ.upd b .unit) t' ns := ht.congr fun k hk => by
        simp only [BoLo.Heap.upd]
        rw [if_neg (by rintro rfl; exact hb_ns hk)]
      obtain ⟨rfl, hlt, hμ₂, hfr₂⟩ := fold_shape hg hfr ns hμb htl hnd' hrec
      -- the algebra: `g` on `a`, then `b` refilled
      rw [steps_beta_iff, algR_subst, steps_alg_cons_iff hg htc] at h₂
      obtain ⟨μ₃, hga, hb₃, rfl, rfl⟩ := h₂
      have ha₂ : ∃ x, μ₂ a = some x := by
        refine ⟨x, ?_⟩
        rw [hfr₂ a (fun h => ha_ns (mem_cells_of_fst h))]
        simp [BoLo.Heap.upd, hab, ha]
      obtain ⟨hμ₃, ha₃, hfr₃⟩ := hfr hμ₂ ha₂ hga
      refine ⟨rfl, ⟨rfl, ?_, r', ?_, ?_⟩, hμ₃.upd htc, ?_⟩
      · obtain ⟨y, hy⟩ := ha₃
        exact ⟨y, by simp [BoLo.Heap.upd, hab, hy]⟩
      · simp [BoLo.Heap.upd]
      · refine hlt.congr fun k hk => ?_
        have hkb : k ≠ b := by rintro rfl; exact hb_ns hk
        have hka : k ≠ a := by rintro rfl; exact ha_ns hk
        simp only [BoLo.Heap.upd, if_neg hkb]
        exact hfr₃ k hka
      · intro k hk
        simp only [List.map_cons, List.mem_cons, not_or] at hk
        by_cases hkb : k = b
        · subst hkb; simp [BoLo.Heap.upd, hb]
        · simp only [BoLo.Heap.upd, if_neg hkb]
          rw [hfr₃ k hk.1, hfr₂ k hk.2]
          simp [BoLo.Heap.upd, hkb]

/-- **The shape law of IterMut**: every run of `iterMut v g` to a value returns `(v, ())`,
leaves the list at the same node cells with every next cell as it was, and changes only the
value cells.  In particular the length is preserved. -/
theorem iterMut_shape {E : VTy} {g : Val} (hg : closedAt 0 g.1 = true) (hfr : ElemFrame g)
    {ns : List (Loc × Loc)} {μ μ' : Heap} {v w : Val} (hμ : HeapClosed μ)
    (hv : ListAt μ v ns) (hnd : (cells ns).Nodup)
    (h : Steps μ (app2 (.val (iterMutV E)) v.1 g.1) μ' w.1) :
    w = .pair v .unit ∧ ListAt μ' v ns ∧ ∀ k, k ∉ ns.map Prod.fst → μ' k = μ k := by
  rw [show Expr.val (iterMutV E) = lam2 (.pair (.app (.app (.val (foldReuseV (clistFE E)))
    (.val (.lam itAlgB))) (.var 1)) unit') from rfl, steps_app2_iff] at h
  have e : ((Expr.pair (.app (.app (.val (foldReuseV (clistFE E))) (.val (.lam itAlgB))) (.var 1))
      unit').subst 1 (v.shift 1 0)).subst 0 g
      = .pair (.app (.app (.val (foldReuseV (clistFE E))) (.val (algG g))) v.1) unit' := by
    simp [itAlgB, algG, itAlgG, app2, unit', closed_subst (foldReuseV_closed _), closed_subst hg,
      closed_shift hg, Expr.subst_shift 0 0 0 g v.1 (le_refl _) (le_refl _),
      closed_subst withborV_closed, closed_subst (show closedAt 0 fillV.1 = true from rfl)]
  rw [e, steps_pairL_iff] at h
  obtain ⟨μm, u, hf, h₂⟩ := h
  rw [steps_appL_iff] at hf
  obtain ⟨μa, f, hfa, hfb⟩ := hf
  rw [show Expr.val (foldReuseV (clistFE E)) = .val (Val.lam
    (.val (.lam (.app (.app (.val (selfR (clistFE E))) (.var 1)) (.var 0))))) from rfl,
    steps_beta_iff, foldReuseV_subst] at hfa
  obtain ⟨rfl, rfl⟩ := steps_val_iff.mp hfa
  obtain ⟨rfl, hl, -, hfr'⟩ := fold_shape hg hfr ns hμ hv hnd hfb
  obtain ⟨u', rfl, h₃⟩ := steps_pairR_iff.mp h₂
  obtain ⟨rfl, rfl⟩ := steps_val_iff (v := Val.unit).mp (by simpa [unit'] using h₃)
  exact ⟨rfl, hl, hfr'⟩

/-! ### The frame hypothesis holds at the program's callback -/

/-- `incCb` as a value. -/
def incCbV : Val :=
  .lam (.val (.lam (.letpair (app2 withswap (.var 0) incG)
    (.seq (.var 0) (.seq (.app forget (.var 1)) unit')))))

theorem incCbV_eq : incCbV.1 = incCb := rfl

/-- `incCb () a` increments the content of `a` and touches nothing else. -/
theorem incCb_frame : ElemFrame incCbV := by
  intro μ μ' a t hμ ha h
  rw [show incCbV.1 = lam2 (.letpair (app2 withswap (.var 0) incG)
    (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))) from rfl, steps_app2_unit_iff] at h
  have e : ((Expr.letpair (app2 withswap (.var 0) incG)
      (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))).subst 1 (Val.unit.shift 1 0)).subst 0
        (Val.loc a)
      = .letpair (app2 withswap (Val.loc a).1 (Val.lam (.pair (.inj₂ (.var 0)) unit')).1)
          (.seq (.var 0) (.seq (.app forget (.var 1)) unit')) := by
    simp [app2, withswap, lam2, incG, forget, unit', v0, v1, v3, load', store']
  rw [e, steps_letpairK_iff] at h
  obtain ⟨μm, v, h₁, h₂⟩ := h
  obtain ⟨ℓ, x, μ₁, x', t', hℓ, hx, hinc, hdom, rfl, rfl⟩ := (steps_withswap_iff rfl).mp h₁
  obtain rfl : a = ℓ := by simpa using hℓ
  rw [steps_beta_iff] at hinc
  have e₂ : (Expr.pair (.inj₂ (.var 0)) unit').subst 0 x = (Val.pair (.inj₂ x) .unit).1 := by
    simp [unit']
  rw [e₂] at hinc
  obtain ⟨rfl, hp⟩ := steps_val_iff.mp hinc
  obtain ⟨rfl, rfl⟩ : x' = .inj₂ x ∧ t' = .unit := by
    have := congrArg Subtype.val hp
    simp only [Val.val_pair, Expr.pair.injEq] at this
    exact ⟨Subtype.ext this.1, Subtype.ext this.2⟩
  rw [steps_letpair_iff] at h₂
  have e₃ : ((Expr.seq (.var 0) (.seq (.app forget (.var 1)) unit')).subst 0
      (Val.unit.shift 1 0)).subst 0 (Val.loc a)
      = .seq Val.unit.1 (.seq (.app forget (Val.loc a).1) unit') := by
    simp [forget, unit']
  rw [e₃, steps_seq_iff, steps_seqK_iff] at h₂
  obtain ⟨μf, u, hfg, hrest⟩ := h₂
  rw [show forget = Expr.val (Val.lam unit') from rfl, steps_beta_iff] at hfg
  obtain ⟨rfl, rfl⟩ := steps_val_iff (v := Val.unit).mp hfg
  obtain ⟨rfl, -⟩ := steps_val_iff (v := Val.unit).mp (steps_seq_iff.mp hrest)
  refine ⟨hμ.upd (by simpa [closedAt] using hμ a x hx), ⟨.inj₂ x, by simp [BoLo.Heap.upd]⟩,
    fun k hk => by simp [BoLo.Heap.upd, hk]⟩

/-- **IterMut's shape law at the program's callback**: incrementing through IterMut keeps every
node where it was. -/
theorem iterInc_shape {ns : List (Loc × Loc)} {μ μ' : Heap} {v w : Val} (hμ : HeapClosed μ)
    (hv : ListAt μ v ns) (hnd : (cells ns).Nodup)
    (h : Steps μ (app2 (.val (iterMutV natN)) v.1 incCbV.1) μ' w.1) :
    w = .pair v .unit ∧ ListAt μ' v ns ∧ ∀ k, k ∉ ns.map Prod.fst → μ' k = μ k :=
  iterMut_shape rfl incCb_frame hμ hv hnd h

end BoCa.Fig16.LogRel.Core.Optics

end
