import FnMut.Core.Sized

/-!
# Core — the borrowed fold as a typing rule  `[spec §6]`

`foldImm : !U(∀'b ⊏ ⊤. A_R ⊸ F R) ⊸ !U(∀'a ⊏ @c. Imm 'a (μX. T) ⊸ F R)` for `T` in the class
`FShape`: `T` is built by `⊗` and `⊕` from closed leaves, `Ref X` and `X`, and is not `X`
itself.  `A_R = T.res 'b R` is the view `Imm̲ 'b T` with every recursive position (`Ref X`, head
`X`) replaced by `R`: the fold makes the recursive calls and the algebra sees their results.

The term is closed and generated from the shape (`travK`, `foldImmV`); recursion is the Z
combinator of `Fix.lean`, so the machine is unchanged.  `foldImm_compatX` is its semantic
typing, by induction on a bound of the borrowed cell's witness size (`withload_sized`), and
inside it on the size of the view value (head `X`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The shapes -/

/-- A `μ` body the borrowed fold covers: `⊗`, `⊕` over closed leaves, `Ref X` and `X`.  `[spec §6]` -/
inductive FShape where
  | leaf (A : VTy)
  | refX
  | varX
  | tensor (F G : FShape)
  | sum (F G : FShape)

/-- The body `T`, with `X` the type variable `0`. -/
def FShape.ty : FShape → VTy
  | .leaf A => A
  | .refX => .ref (.tvar 0)
  | .varX => .tvar 0
  | .tensor F G => .tensor F.ty G.ty
  | .sum F G => .sum F.ty G.ty

/-- `Imm̲ 'y T` with `Rr` at each `Ref X` and `Rh` at each head `X`. -/
def FShape.resRH (y : LifeVar) (Rr Rh : VTy) : FShape → VTy
  | .leaf A => A.immReborrow (.var y)
  | .refX => Rr
  | .varX => Rh
  | .tensor F G => .tensor (F.resRH y Rr Rh) (G.resRH y Rr Rh)
  | .sum F G => .sum (F.resRH y Rr Rh) (G.resRH y Rr Rh)

/-- `A_R`: `Imm̲ 'y T` with `R` at every recursive position. -/
abbrev FShape.res (y : LifeVar) (R : VTy) (F : FShape) : VTy := F.resRH y R R

/-- Every leaf is closed. -/
def FShape.WF : FShape → Prop
  | .leaf A => A.Cl 0
  | .refX => True
  | .varX => True
  | .tensor F G => F.WF ∧ G.WF
  | .sum F G => F.WF ∧ G.WF

/-- The body is not `X` itself. -/
def FShape.Guarded : FShape → Prop
  | .varX => False
  | _ => True

theorem FShape.Cl_ty : ∀ {F : FShape}, F.WF → F.ty.Cl 1
  | .leaf A, h => VTy.Cl_mono A h (Nat.zero_le _)
  | .refX, _ => Nat.zero_lt_one
  | .varX, _ => Nat.zero_lt_one
  | .tensor _ _, h => ⟨Cl_ty h.1, Cl_ty h.2⟩
  | .sum _ _, h => ⟨Cl_ty h.1, Cl_ty h.2⟩

theorem FShape.noMut_ty : ∀ {F : FShape}, F.WF → F.ty.NoMut 0
  | .leaf A, h => VTy.noMut_of_not_occ A (VTy.not_occ_of_Cl A h (Nat.zero_le _))
  | .refX, _ => trivial
  | .varX, _ => trivial
  | .tensor _ _, h => ⟨noMut_ty h.1, noMut_ty h.2⟩
  | .sum _ _, h => ⟨noMut_ty h.1, noMut_ty h.2⟩

/-- **`A_R` is the unrolled view with the recursive positions replaced.**  The view `withload`
hands over at `Imm 'y M`, `M = μX. T`, unrolled, is `Imm̲ 'y (T[M/X])`: it has `Imm 'y M` at each
`Ref X` and `Imm̲ 'y M` at each head `X`, and is `T.resRH` at those two types. -/
theorem FShape.view_eq {M : VTy} (y : LifeVar) :
    ∀ {F : FShape}, F.WF →
      (VTy.inst M F.ty).immReborrow (.var y) = F.resRH y (.imm (.var y) M) (M.immReborrow (.var y))
  | .leaf A, h => by
      show (VTy.inst M A).immReborrow (.var y) = A.immReborrow (.var y)
      rw [show VTy.inst M A = A from VTy.subst_closed0 h _]
  | .refX, _ => rfl
  | .varX, _ => rfl
  | .tensor _ _, h => congrArg₂ VTy.tensor (view_eq y h.1) (view_eq y h.2)
  | .sum _ _, h => congrArg₂ VTy.sum (view_eq y h.1) (view_eq y h.2)

/-- The algebra's type, `!U(∀'y ⊏ ⊤. A_R ⊸ F R)`. -/
abbrev algTy (F : FShape) (y : LifeVar) (R : VTy) : VTy :=
  .bang (VTy.all y LifeCtx.empty.meetOfDom (VTy.lolli (F.res y R) R))

/-- The fold's type, `!U(∀'y ⊏ @c. Imm 'y (μX. T) ⊸ F R)`. -/
abbrev foldTy (F : FShape) (y : LifeVar) (c : Lifetime.Life) (R : VTy) : VTy :=
  .bang (VTy.all y c (VTy.lolli (.imm (.var y) (.mu F.ty)) R))

/-! ### The term -/

/-- `M to x. N`, written `(λx. N) M`. -/
def bindE (M N : Expr) : Expr := .app (.val (.lam N)) M

/-- `travK G h w`: the traversal of a view `w` at the shape `G`, with `h` the recursive call on
a view of `μX. T`.  At a leaf `w`; at `Ref X` `withload w (λ_. h)`; at `X` `h w`; at `⊗` and
`⊕` componentwise. -/
def travK : FShape → Val
  | .leaf _ => .lam (.val (.lam (.var 0)))
  | .refX => .lam (.val (.lam (.app (.app withload (.var 0)) (.val (.lam (.var 2))))))
  | .varX => .lam (.val (.lam (.app (.var 1) (.var 0))))
  | .tensor F G => .lam (.val (.lam (.letpair (.var 0)
      (bindE (.app (.app (.val (travK F)) (.var 3)) (.var 1))
        (bindE (.app (.app (.val (travK G)) (.var 4)) (.var 1))
          (.pair (.var 1) (.var 0)))))))
  | .sum F G => .lam (.val (.lam (.case (.var 0)
      (bindE (.app (.app (.val (travK F)) (.var 2)) (.var 0)) (.inj₁ (.var 0)))
      (bindE (.app (.app (.val (travK G)) (.var 2)) (.var 0)) (.inj₂ (.var 0))))))

theorem travK_closed : ∀ F : FShape, closedAt 0 (travK F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travK, bindE, closedAt, closedAt_mono _ (travK_closed F) (Nat.zero_le _),
        closedAt_mono _ (travK_closed G) (Nat.zero_le _)]
  | .sum F G => by
      simp [travK, bindE, closedAt, closedAt_mono _ (travK_closed F) (Nat.zero_le _),
        closedAt_mono _ (travK_closed G) (Nat.zero_le _)]

/-- The body of `fold = Z (λself. λg. λu. travK T (λw. self g w) u to r. g [] r)`. -/
def fB (F : FShape) : Expr := .val (.lam (bindE
  (.app (.app (.val (travK F)) (.val (.lam (.app (.app (.var 3) (.var 2)) (.var 0))))) (.var 0))
  (.app (.app (.var 2) (.val .unit)) (.var 0))))

theorem fB_closed (F : FShape) : closedAt 2 (fB F) = true := by
  simp [fB, bindE, closedAt, closedAt_mono _ (travK_closed F) (Nat.zero_le _)]

/-- The recursive handle. -/
abbrev selfF (F : FShape) : Val := selfV (fB F)

theorem selfF_closed (F : FShape) : closedAt 0 (selfF F).1 = true := selfV_closed (fB_closed F)

/-- `λw. self g w` at the handle, for an algebra `g`. -/
def hV (F : FShape) (g : Val) : Val := .lam (.app (.app (.val (selfF F)) (.val (g.shift 1 0))) (.var 0))

/-- **`foldImm = λg. Λ. λl. travK (Ref X) (λw. self g w) l`**, a closed value. -/
def foldImmV (F : FShape) : Val := .lam (.val (.lam (.val (.lam
  (.app (.app (.val (travK .refX)) (.val (.lam (.app (.app (.val (selfF F)) (.var 3)) (.var 0)))))
    (.var 0))))))

theorem foldImmV_closed (F : FShape) : closedAt 0 (foldImmV F).1 = true := by
  simp [foldImmV, closedAt, closedAt_mono _ (travK_closed .refX) (Nat.zero_le _),
    closedAt_mono _ (selfF_closed F) (Nat.zero_le _)]

/-! ### Substitution -/

theorem subst_shift_succ {j d : Nat} (s : Val) (e : Expr) (h : j ≤ d) :
    Expr.subst j s (Expr.shift (d + 1) 0 e) = Expr.shift d 0 e :=
  Expr.subst_shift d 0 j s e (Nat.zero_le _) (by omega)

theorem closed_subst {v : Val} (h : closedAt 0 v.1 = true) (j : Nat) (s : Val) :
    Expr.subst j s v.1 = v.1 := subst_closedAt v.1 s h (Nat.zero_le j)

theorem closed_shift {v : Val} (h : closedAt 0 v.1 = true) (d c : Nat) :
    Expr.shift d c v.1 = v.1 := shift_closedAt v.1 d h (Nat.zero_le c)

/-- The body of `travK G` under its two binders (`h` = 1, `w` = 0). -/
def tB : FShape → Expr
  | .leaf _ => .var 0
  | .refX => .app (.app withload (.var 0)) (.val (.lam (.var 2)))
  | .varX => .app (.var 1) (.var 0)
  | .tensor F G => .letpair (.var 0)
      (bindE (.app (.app (.val (travK F)) (.var 3)) (.var 1))
        (bindE (.app (.app (.val (travK G)) (.var 4)) (.var 1))
          (.pair (.var 1) (.var 0))))
  | .sum F G => .case (.var 0)
      (bindE (.app (.app (.val (travK F)) (.var 2)) (.var 0)) (.inj₁ (.var 0)))
      (bindE (.app (.app (.val (travK G)) (.var 2)) (.var 0)) (.inj₂ (.var 0)))

theorem travK_eq (G : FShape) : travK G = .lam (.val (.lam (tB G))) := by cases G <;> rfl

theorem withload_closed : closedAt 0 withload = true := rfl

/-! ### The measure at the positions of a view -/

/-- Every `Ref` position of `w : A` holds, in `χ`, a cell whose witness has fewer than `n`
cells. -/
def Good (A : VTy) (w : Val) (χ : WRes) (n : Nat) : Prop :=
  ∀ l S, RefPos A w l S → ∀ ψ, χ.get l = some ψ → dsize ψ.wit < n

theorem Good.tensorL {A B : VTy} {v₁ v₂ : Val} {χ χ₁ χ₂ : WRes} {n : Nat}
    (h : Good (.tensor A B) (.pair v₁ v₂) χ n) (hc : ResU.CompS χ₁ χ₂ χ) : Good A v₁ χ₁ n :=
  fun l S hp ψ e => by
    obtain ⟨ψ', e', -, hw, -⟩ := compS_get_left' hc e
    rw [← hw]; exact h l S (.tensorL hp) ψ' e'

theorem Good.tensorR {A B : VTy} {v₁ v₂ : Val} {χ χ₁ χ₂ : WRes} {n : Nat}
    (h : Good (.tensor A B) (.pair v₁ v₂) χ n) (hc : ResU.CompS χ₁ χ₂ χ) : Good B v₂ χ₂ n :=
  fun l S hp ψ e => by
    obtain ⟨ψ', e', -, hw, -⟩ := compS_get_right' hc e
    rw [← hw]; exact h l S (.tensorR hp) ψ' e'

theorem Good.sumL {A B : VTy} {v : Val} {χ : WRes} {n : Nat}
    (h : Good (.sum A B) (.inj₁ v) χ n) : Good A v χ n :=
  fun l S hp ψ e => h l S (.sumL hp) ψ e

theorem Good.sumR {A B : VTy} {v : Val} {χ : WRes} {n : Nat}
    (h : Good (.sum A B) (.inj₂ v) χ n) : Good B v χ n :=
  fun l S hp ψ e => h l S (.sumR hp) ψ e

theorem Good.unroll {A : VTy} {w : Val} {χ : WRes} {n : Nat} (hc : (VTy.mu A).Cl 0)
    (h : Good (.mu A) w χ n) : Good (VTy.inst (.mu A) A) w χ n :=
  fun l S hp ψ e => h l S (.mu hc hp) ψ e

theorem Good.mono {A : VTy} {w : Val} {χ : WRes} {n m : Nat} (h : Good A w χ n) (hnm : n ≤ m) :
    Good A w χ m :=
  fun l S hp ψ e => lt_of_lt_of_le (h l S hp ψ e) hnm

/-- At a `Ref M` position the borrow's witness is below the bound. -/
theorem Good.witLt {M : VTy} {ℓ : Loc} {χ : WRes} {n : Nat} (h : Good (.ref M) (.loc ℓ) χ n) :
    WitLt ℓ χ n := by
  intro s u σ hσ hχ
  have e : χ.get ℓ = some (CellU.immOf s u σ hσ) := by rw [hχ]; exact ResU.single_get_self _ _
  simpa using h ℓ M (RefPos.ref M ℓ) _ e

/-- **The view `withload` hands over is `Good` at the loaded witness's size.**  At a `Ref`
position `ℓ` of the observable value, the witness `σ` holds `ℓ ↦ own(u)` (`own_split`), and the
view's cell there is `imm({β}, u, q/ℓ)` for a piece `q ≤ σ` holding `ℓ` (`typed_image_pos`), so
its witness is smaller than `σ` (`dsize_del_lt`). -/
theorem good_of_image {M : VTy} {x : LifeVar} {δ : LSub} {ls ls' : List SRec} {β : Life}
    {w : Val} {σ χ : WRes} (hx : ¬ VFree x M) (hobs : vC false M ls δ w σ)
    (hreb : ResU.Reb β σ χ)
    (hview : vC true (M.immReborrow (.var x)) ls' (δ.extend x β) w χ) :
    Good M w χ (dsize σ) := by
  intro l S hp ψ e
  obtain ⟨u, P, B, hB, -, hle⟩ := own_split M (vC_vShape false M hobs) hp
  have hown : σ.get l = some (CellU.ownOf u) :=
    own_of_le hle (ResU.CompS.get_left_of_ne_imm hB (ResU.single_get_self _ _) (by simp)).2
  obtain ⟨q, hq, eχ, hqσ, hql, -⟩ :=
    typed_image_pos hx hp hown hreb (vC_vShape true _ hview)
  rw [eχ] at e
  cases Option.some.inj e
  simpa using dsize_del_lt hqσ hql

/-! ### Reduction -/

theorem models_empty_any (δ : LSub) : LifeCtx.empty.Models δ := fun _ _ h => by
  simp [LifeCtx.find?, LifeCtx.empty, Lifetime.assocFind] at h

/-- `λ_. h`, the callback `travK (Ref X)` hands to `withload`. -/
def cbOf (h : Val) : Val := .lam (h.1.shift 1 0)

/-- `cbOf h [] w` reaches `h w`. -/
theorem cbOf_app (h w : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.app (.val h) (.val w)) Q)
      (wpTS ls (.app (.app (.val (cbOf h)) (.val .unit)) (.val w)) Q) := by
  intro ρ hw
  refine wpTS_beta_in (.appL .hole w) _ Val.unit ls Q ρ ?_
  have e : Expr.subst 0 Val.unit (h.1.shift 1 0) = h.1 := by
    rw [subst_shift_succ _ _ (Nat.le_refl 0), Expr.shift_zero]
  simpa [Kont.plug, e] using hw

/-- `travK G h w` reaches `tB G` with `h` and `w` substituted. -/
theorem travK_app (G : FShape) (h w : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (((tB G).subst 1 (h.shift 1 0)).subst 0 w) Q)
      (wpTS ls (.app (.app (.val (travK G)) (.val h)) (.val w)) Q) := by
  intro ρ hw
  rw [travK_eq]
  refine wpTS_beta_in (.appL .hole w) _ h ls Q ρ ?_
  exact wpTS_lolli ls _ w Q ρ hw

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

theorem tB_leaf (A : VTy) (h w : Val) :
    ((tB (.leaf A)).subst 1 (h.shift 1 0)).subst 0 w = .val w := by simp [tB]

theorem tB_refX (h w : Val) :
    ((tB .refX).subst 1 (h.shift 1 0)).subst 0 w = .app (.app withload (.val w)) (.val (cbOf h)) := by
  simp [tB, cbOf, subst_shift_succ, subst_closedAt withload _ withload_closed (Nat.zero_le _)]

theorem tB_varX (h w : Val) :
    ((tB .varX).subst 1 (h.shift 1 0)).subst 0 w = .app (.val h) (.val w) := by
  simp [tB, subst_shift_succ]

theorem tB_tensor (F G : FShape) (h v₁ v₂ : Val) :
    ((((tB (.tensor F G)).subst 1 (h.shift 1 0)).subst 0 (Val.pair v₁ v₂)))
      = .letpair (.val (Val.pair v₁ v₂))
          (bindE (.app (.app (.val (travK F)) (.val (h.shift 2 0))) (.var 1))
            (bindE (.app (.app (.val (travK G)) (.val (h.shift 3 0))) (.var 1))
              (.pair (.var 1) (.var 0)))) := by
  simp [tB, bindE, closed_subst (travK_closed _), subst_shift_succ]

theorem tensor_body (F G : FShape) (h v₁ v₂ : Val) :
    ((bindE (.app (.app (.val (travK F)) (.val (h.shift 2 0))) (.var 1))
        (bindE (.app (.app (.val (travK G)) (.val (h.shift 3 0))) (.var 1))
          (.pair (.var 1) (.var 0)))).subst 0 (v₂.shift 1 0)).subst 0 v₁
      = (Kont.appR (.val (.lam (bindE (.app (.app (.val (travK G)) (.val (h.shift 1 0)))
          (.val (v₂.shift 1 0))) (.pair (.var 1) (.var 0))))) .hole).plug
          (.app (.app (.val (travK F)) (.val h)) (.val v₁)) := by
  simp [bindE, Kont.plug, closed_subst (travK_closed _), subst_shift_succ]

theorem tensor_body₂ (G : FShape) (h v₂ r₁ : Val) :
    (bindE (.app (.app (.val (travK G)) (.val (h.shift 1 0))) (.val (v₂.shift 1 0)))
        (.pair (.var 1) (.var 0))).subst 0 r₁
      = (Kont.appR (.val (.lam (.pair (.val (r₁.shift 1 0)) (.var 0)))) .hole).plug
          (.app (.app (.val (travK G)) (.val h)) (.val v₂)) := by
  simp [bindE, Kont.plug, closed_subst (travK_closed _), subst_shift_succ]

theorem tensor_body₃ (r₁ r₂ : Val) :
    (Expr.pair (.val (r₁.shift 1 0)) (.var 0)).subst 0 r₂ = .val (Val.pair r₁ r₂) := by
  simp [subst_shift_succ]

theorem tB_sum (F G : FShape) (h w : Val) :
    ((tB (.sum F G)).subst 1 (h.shift 1 0)).subst 0 w
      = .case (.val w)
          (bindE (.app (.app (.val (travK F)) (.val (h.shift 1 0))) (.var 0)) (.inj₁ (.var 0)))
          (bindE (.app (.app (.val (travK G)) (.val (h.shift 1 0))) (.var 0)) (.inj₂ (.var 0))) := by
  simp [tB, bindE, closed_subst (travK_closed _), subst_shift_succ]

theorem sum_branch (F : FShape) (h v : Val) (inj : Expr → Expr)
    (hinj : ∀ j s e, Expr.subst j s (inj e) = inj (Expr.subst j s e)) :
    (bindE (.app (.app (.val (travK F)) (.val (h.shift 1 0))) (.var 0)) (inj (.var 0))).subst 0 v
      = (Kont.appR (.val (.lam (inj (.var 0)))) .hole).plug
          (.app (.app (.val (travK F)) (.val h)) (.val v)) := by
  simp [bindE, Kont.plug, closed_subst (travK_closed _), subst_shift_succ, hinj]

/-! ### The traversal -/

/-- The recursive call through a sub-borrow `Imm 'y M` at witness size below `n`: `withload`
with the callback `λ_. h`. -/
def PSpec (M R : VTy) (y : LifeVar) (δ : LSub) (n : Nat) (h : Val) : Prop :=
  ∀ α ℓ ρ ls, vP (.imm (.var y) M) ls (δ.extend y α) (.loc ℓ) ρ → WitLt ℓ ρ n →
    wpTS ls (.app (.app withload (.val (.loc ℓ))) (.val (cbOf h))) (fun ls' v => vP R ls' δ v) ρ

/-- The recursive call `h w` on a view `w` of `M` at `β` smaller than `K`. -/
def HSpec (M R : VTy) (y : LifeVar) (δ : LSub) (β : Life) (n K : Nat) (h : Val) : Prop :=
  ∀ w χ ls, sizeOf w.1 < K → vC true (M.immReborrow (.var y)) ls (δ.extend y β) w χ →
    Good M w χ n → wpTS ls (.app (.val h) (.val w)) (fun ls' v => vP R ls' δ v) χ

theorem vP_ext {R : VTy} {y : LifeVar} (hy : ¬ VFree y R) {ls : List SRec} {δ : LSub}
    {β : Life} {v : Val} {ρ : WRes} : vP R ls (δ.extend y β) v ρ ↔ vP R ls δ v ρ :=
  Iff.of_eq (congrFun (congrFun (vC_extend_of_not_free hy true ls δ β) v) ρ)

theorem sizeOf_pair (v₁ v₂ : Val) :
    sizeOf (Val.pair v₁ v₂).1 = 1 + sizeOf v₁.1 + sizeOf v₂.1 := rfl

/-- **The traversal.**  At a sub-shape `G` of the body, `travK G h w` takes a view `w` of
`G[M/X]` at `β` to a value of `G.res 'y R`, given the recursive call through a sub-borrow
(`PSpec`) and on a smaller view (`HSpec`).  Induction on `G`. -/
theorem trav_spec {M R : VTy} {y : LifeVar} {δ : LSub} {β : Life} {n K : Nat} {h : Val}
    (hyR : ¬ VFree y R) (hP : PSpec M R y δ n h) (hH : HSpec M R y δ β n K h) :
    ∀ (G : FShape), G.WF → ∀ w χ ls, sizeOf w.1 ≤ K → (G = .varX → sizeOf w.1 < K) →
      vC true ((VTy.inst M G.ty).immReborrow (.var y)) ls (δ.extend y β) w χ →
      Good (VTy.inst M G.ty) w χ n →
      wpTS ls (.app (.app (.val (travK G)) (.val h)) (.val w))
        (fun ls' r => vP (G.res y R) ls' (δ.extend y β) r) χ
  | .leaf A, hA, w, χ, ls, _, _, hview, _ => by
      refine travK_app _ h w ls _ χ ?_
      rw [tB_leaf]
      have e : VTy.inst M A = A := VTy.subst_closed0 hA _
      simp only [FShape.ty, e] at hview
      exact wpTS_val ls w _ χ hview
  | .refX, _, w, χ, ls, _, _, hview, hgood => by
      refine travK_app _ h w ls _ χ ?_
      rw [tB_refX]
      change vP (.imm (.var y) M) ls (δ.extend y β) w χ at hview
      obtain ⟨ℓ, rfl⟩ : ∃ ℓ, w = Val.loc ℓ := by
        obtain ⟨α₀, -, ℓ, hs₁⟩ := hview
        exact ⟨ℓ, (pure_sep_iff.mp hs₁).1.1⟩
      refine wpTS_mono (fun ls' v ρ hv => ?_) χ (hP β ℓ χ ls hview (Good.witLt hgood))
      exact (vP_ext hyR).mpr hv
  | .varX, _, w, χ, ls, _, hlt, hview, hgood => by
      refine travK_app _ h w ls _ χ ?_
      rw [tB_varX]
      refine wpTS_mono (fun ls' v ρ hv => ?_) χ (hH w χ ls (hlt rfl) hview hgood)
      exact (vP_ext hyR).mpr hv
  | .tensor F G, hFG, w, χ, ls, hK, _, hview, hgood => by
      obtain ⟨v₁, v₂, hs⟩ := hview
      obtain ⟨hw, χ₁, χ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      subst hw
      have hs₁ : sizeOf v₁.1 < K := by rw [sizeOf_pair] at hK; omega
      have hs₂ : sizeOf v₂.1 < K := by rw [sizeOf_pair] at hK; omega
      refine travK_app _ h _ ls _ χ ?_
      rw [tB_tensor]
      refine wpTS_tensor ls v₁ v₂ _ _ χ ?_
      rw [tensor_body]
      refine wpTS_bind_frame _ _ ls (fun ls' r => vP (F.res y R) ls' (δ.extend y β) r)
        (fun ls' ρ => vP ((VTy.inst M G.ty).immReborrow (.var y)) ls' (δ.extend y β) v₂ ρ ∧
          Good (VTy.inst M G.ty) v₂ ρ n)
        _ (fun ls' hls ρ hρ => ⟨vP_same hls hρ.1, hρ.2⟩) ?_ χ
        ⟨χ₁, χ₂, hc, trav_spec hyR hP hH F hFG.1 v₁ χ₁ ls (le_of_lt hs₁) (fun _ => hs₁) h₁
          (Good.tensorL hgood hc), h₂, Good.tensorR hgood hc⟩
      rintro ls' hls r₁ σ ⟨σ₁, σ₂, hcσ, hr₁, hv₂, hg₂⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ r₁ _ σ ?_
      rw [tensor_body₂]
      refine wpTS_bind_frame _ _ ls' (fun ls'' r => vP (G.res y R) ls'' (δ.extend y β) r)
        (fun ls'' => vP (F.res y R) ls'' (δ.extend y β) r₁)
        _ (fun ls'' hls' ρ hρ => vP_same hls' hρ) ?_ σ
        ⟨σ₂, σ₁, ResU.CompS.comm hcσ, trav_spec hyR hP hH G hFG.2 v₂ σ₂ ls' (le_of_lt hs₂)
          (fun _ => hs₂) hv₂ hg₂, hr₁⟩
      rintro ls'' - r₂ τ ⟨τ₁, τ₂, hcτ, hr₂, hr₁'⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ r₂ _ τ ?_
      rw [tensor_body₃]
      exact wpTS_val ls'' _ _ τ ⟨r₁, r₂, pure_sep_iff.mpr ⟨rfl, τ₂, τ₁, ResU.CompS.comm hcτ, hr₁', hr₂⟩⟩
  | .sum F G, hFG, w, χ, ls, hK, _, hview, hgood => by
      rcases hview with ⟨v, hs⟩ | ⟨v, hs⟩
      · obtain ⟨hw, hv⟩ := pure_sep_iff.mp hs
        subst hw
        have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₁ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine travK_app _ h _ ls _ χ ?_
        rw [tB_sum]
        refine wpTS_sum₁ ls v _ _ _ χ ?_
        rw [sum_branch F h v Expr.inj₁ (fun _ _ _ => rfl)]
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (trav_spec hyR hP hH F hFG.1 v χ ls (le_of_lt hsz) (fun _ => hsz) hv (Good.sumL hgood))
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        exact wpTS_val ls' (Val.inj₁ r) _ ρ (Or.inl ⟨r, pure_sep_iff.mpr ⟨rfl, hr⟩⟩)
      · obtain ⟨hw, hv⟩ := pure_sep_iff.mp hs
        subst hw
        have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₂ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine travK_app _ h _ ls _ χ ?_
        rw [tB_sum]
        refine wpTS_sum₂ ls v _ _ _ χ ?_
        rw [sum_branch G h v Expr.inj₂ (fun _ _ _ => rfl)]
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (trav_spec hyR hP hH G hFG.2 v χ ls (le_of_lt hsz) (fun _ => hsz) hv (Good.sumR hgood))
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        exact wpTS_val ls' (Val.inj₂ r) _ ρ (Or.inr ⟨r, pure_sep_iff.mpr ⟨rfl, hr⟩⟩)

/-! ### The recursive function -/

/-- `fB` at a closed handle `S` and an algebra `g`, applied to `w`. -/
theorem fB_subst (F : FShape) {S : Val} (hS : closedAt 0 S.1 = true) (g w : Val) :
    (Kont.appL .hole w).plug (((fB F).subst 1 S).subst 0 g)
      = .app (.val (.lam (bindE (.app (.app (.val (travK F))
          (.val (.lam (.app (.app (.val S) (.val (g.shift 2 0))) (.var 0))))) (.var 0))
          (.app (.app (.val (g.shift 2 0)) (.val .unit)) (.var 0))))) (.val w) := by
  simp [Kont.plug, fB, bindE, closed_subst (travK_closed _), closed_subst hS, closed_shift hS]

theorem fB_body (F : FShape) {S : Val} (hS : closedAt 0 S.1 = true) (g w : Val) :
    (bindE (.app (.app (.val (travK F))
          (.val (.lam (.app (.app (.val S) (.val (g.shift 2 0))) (.var 0))))) (.var 0))
          (.app (.app (.val (g.shift 2 0)) (.val .unit)) (.var 0))).subst 0 w
      = (Kont.appR (.val (.lam (.app (.app (.val (g.shift 1 0)) (.val .unit)) (.var 0)))) .hole).plug
          (.app (.app (.val (travK F)) (.val (.lam (.app (.app (.val S) (.val (g.shift 1 0)))
            (.var 0))))) (.val w)) := by
  simp [Kont.plug, bindE, closed_subst (travK_closed _), closed_subst hS, subst_shift_succ]

/-- `h w` for `h = λw. self g w` reaches `travK T h w to r. g [] r`. -/
theorem hV_app (F : FShape) (g w : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls ((Kont.appR (.val (.lam (.app (.app (.val (g.shift 1 0)) (.val .unit))
        (.var 0)))) .hole).plug (.app (.app (.val (travK F)) (.val (hV F g))) (.val w))) Q)
      (wpTS ls (.app (.val (hV F g)) (.val w)) Q) := by
  intro ρ hw
  refine wpTS_lolli _ _ w Q ρ ?_
  have e₁ : Expr.subst 0 w (.app (.app (.val (selfF F)) (.val (g.shift 1 0))) (.var 0))
      = .app (.app (.val (selfF F)) (.val g)) (.val w) := by
    simp [closed_subst (selfF_closed F), subst_shift_succ]
  rw [e₁]
  refine wpTS_selfV_in (fB_closed F) (.appL .hole w) g ls Q ρ ?_
  rw [fixV_eq (fB_closed F)]
  refine wpTS_beta_in (.appL .hole w) _ g ls Q ρ ?_
  rw [fB_subst F (selfF_closed F)]
  refine wpTS_lolli _ _ w Q ρ ?_
  rw [fB_body F (selfF_closed F)]
  exact hw

/-- The algebra applied: `g [] r` at `β ⊏ ⊤` runs to a value of `R`. -/
theorem alg_call {A R : VTy} {y : LifeVar} {δ : LSub} {ls : List SRec} {g r : Val} {β : Life}
    {ρ : WRes} (hyR : ¬ VFree y R) (hβ : LtLife δ LifeCtx.empty.meetOfDom β)
    (hg : vC true (.bang (VTy.all y LifeCtx.empty.meetOfDom (VTy.lolli A R))) ls δ g PMap.empty)
    (hr : vP A ls (δ.extend y β) r ρ) :
    wpTS ls (.app (.app (.val g) (.val .unit)) (.val r)) (fun ls' v => vP R ls' δ v) ρ := by
  obtain ⟨-, hthunk⟩ := hg
  have hwp := hthunk ls (Ext.refl _ _) β PMap.empty PMap.empty ⟨rfl, hβ⟩
    (ResU.comp_empty_right _)
  refine wpTS_bind_frame (.appL .hole r) (.app (.val g) (.val .unit)) ls
    (fun ls' f => vP (VTy.lolli A R) ls' (δ.extend y β) f)
    (fun ls' => vP A ls' (δ.extend y β) r) _ (fun ls' hls ρ h => vP_same hls h) ?_ ρ
    ⟨PMap.empty, ρ, ResU.CompS.comm (ResU.comp_empty_right ρ), hwp, hr⟩
  rintro ls' - f σ ⟨σ₁, σ₂, hcσ, hf, hr'⟩
  simp only [Kont.plug]
  refine wpTS_mono (fun ls'' v ρ' hv => (vP_ext hyR).mp hv) σ
    (hf ls' (Ext.refl _ _) r σ₂ σ hr' hcσ)

/-! ### Induction on the witness size, then on the view -/

theorem find?_extend_twice (δ : LSub) (y : LifeVar) (α β : Life) (z : LifeVar) :
    ((δ.extend y α).extend y β).find? z = (δ.extend y β).find? z := by
  by_cases h : y = z
  · subst h; rw [find?_extend_self, find?_extend_self]
  · rw [find?_extend_ne _ _ h, find?_extend_ne _ _ h, find?_extend_ne _ _ h]

/-- No borrow has a witness of fewer than `0` cells. -/
theorem pSpec_zero {M R : VTy} {y : LifeVar} {δ : LSub} {h : Val} : PSpec M R y δ 0 h := by
  intro α ℓ ρ ls hv hn
  obtain ⟨α₀, -, ℓ', hs⟩ := hv
  obtain ⟨⟨hℓ', -⟩, himm⟩ := pure_sep_iff.mp hs
  obtain ⟨s, u, σ, hσ, hρ, -⟩ := ptoImmO_toImm himm
  exact absurd (hn s u σ hσ (by
    have e : ℓ' = ℓ := by have := congrArg Subtype.val hℓ'; simpa using this.symm
    rw [hρ, e])) (Nat.not_lt_zero _)

/-- **A sub-borrow at witness size below `m + 1`.**  `withload_sized` at the borrow; the view
it hands over is `Good` at the loaded witness's size (`good_of_image`), which is at most `m`,
so the recursive call on the view at level `m` applies.  Its result leaves the callback's
`['x]` because `R` outlives every lifetime (6.60). -/
theorem pSpec_succ {M R : VTy} {y : LifeVar} {δ : LSub} {m : Nat} {h : Val}
    (hyM : ¬ VFree y M) (hyR : ¬ VFree y R) (hR : ∀ Δ a, VOutlives Δ a R)
    (hH : ∀ β, LtLife δ LifeCtx.empty.meetOfDom β → ∀ K, HSpec M R y δ β m K h) :
    PSpec M R y δ (m + 1) h := by
  intro α ℓ ρ ls hv hn
  refine withload_sized (T₁ := M) y hyM Lifetime.SLife.top (fun σ => dsize σ < m + 1)
    (fun ls' v => vP R ls' δ v) hv hn (ResU.comp_empty_right ρ) ?_
  intro β w χ ρ' hβ hview ⟨σ, hKσ, hobs, hreb⟩ hcomp
  rw [eq_of_compS_empty_left hcomp]
  refine cbOf_app h w ls _ χ ?_
  have hgood := (good_of_image hyM hobs hreb hview).mono (Nat.lt_succ_iff.mp hKσ)
  have e := vC_congr (M.immReborrow (.var y)) (δ₁ := (δ.extend y α).extend y β)
    (δ₂ := δ.extend y β) (fun z _ => find?_extend_twice δ y α β z) true ls
  rw [e] at hview
  refine wpTS_mono (fun ls' v ρ₀ hv => ⟨hv, ?_⟩) χ
    (hH β ⟨_, rfl, hβ⟩ (sizeOf w.1 + 1) w χ ls (Nat.lt_succ_self _) hview hgood)
  exact vC_outlives (Δ := LifeCtx.empty) (a := .var y) (models_empty_any _)
    (find?_extend_self δ y β) (hR _ _) true ls' v ρ₀ ((vP_ext hyR).mpr hv)

theorem alg_subst (g r : Val) :
    Expr.subst 0 r (.app (.app (.val (g.shift 1 0)) (.val .unit)) (.var 0))
      = .app (.app (.val g) (.val .unit)) (.val r) := by
  simp [subst_shift_succ]

/-- **The recursive call on a view**, at every witness bound `n`: induction on `n`, and at each
`n` on a bound `K` of the view value's size. -/
theorem hSpec_all {F : FShape} (hF : F.WF) (hG : F.Guarded) {y : LifeVar} {R : VTy} {δ : LSub}
    {g : Val} (hyM : ¬ VFree y (.mu F.ty)) (hyR : ¬ VFree y R) (hR : ∀ Δ a, VOutlives Δ a R)
    (hg : ∀ ls, vC true (algTy F y R) ls δ g PMap.empty) :
    ∀ n β, LtLife δ LifeCtx.empty.meetOfDom β → ∀ K, HSpec (.mu F.ty) R y δ β n K (hV F g) := by
  have step : ∀ n, PSpec (.mu F.ty) R y δ n (hV F g) →
      ∀ β, LtLife δ LifeCtx.empty.meetOfDom β → ∀ K, HSpec (.mu F.ty) R y δ β n K (hV F g) := by
    intro n hP β hβ K
    induction K with
    | zero => intro w χ ls hlt; exact absurd hlt (Nat.not_lt_zero _)
    | succ K ihK =>
        intro w χ ls hlt hview hgood
        refine hV_app F g w ls _ χ ?_
        refine wpTS_bind _ _ ls _ χ ?_
        have hview' := (vC_immReborrow_mu_iff (A := F.ty) (FShape.Cl_ty hF) (.var y) true ls
          (δ.extend y β) w χ).mp hview
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (trav_spec hyR hP ihK F hF w χ ls (Nat.lt_succ_iff.mp hlt)
            (fun e => by subst e; exact hG.elim) hview' (hgood.unroll (FShape.Cl_ty hF)))
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        rw [alg_subst]
        exact alg_call hyR hβ (hg ls') hr
  intro n
  induction n with
  | zero => exact step 0 pSpec_zero
  | succ m ih => exact step (m + 1) (pSpec_succ hyM hyR hR ih)

theorem pSpec_all {F : FShape} (hF : F.WF) (hG : F.Guarded) {y : LifeVar} {R : VTy} {δ : LSub}
    {g : Val} (hyM : ¬ VFree y (.mu F.ty)) (hyR : ¬ VFree y R) (hR : ∀ Δ a, VOutlives Δ a R)
    (hg : ∀ ls, vC true (algTy F y R) ls δ g PMap.empty) :
    ∀ n, PSpec (.mu F.ty) R y δ n (hV F g)
  | 0 => pSpec_zero
  | m + 1 => pSpec_succ hyM hyR hR (hSpec_all hF hG hyM hyR hR hg m)

/-! ### The rule -/

theorem ext_empty (ls ls' : List SRec) : Ext ls ls' PMap.empty :=
  ⟨fun _ _ hr => by obtain ⟨m, ψ, e, -⟩ := hr; simp at e,
   fun _ hb => by obtain ⟨m, ψ, e, -⟩ := hb; simp at e⟩

/-- `foldImm g`, a closure over the algebra. -/
def foldCl (F : FShape) (g : Val) : Val := .lam (.val (.lam
  (.app (.app (.val (travK .refX)) (.val (.lam (.app (.app (.val (selfF F)) (.val (g.shift 3 0)))
    (.var 0))))) (.var 0))))

/-- `foldImm g []`. -/
def foldLam (F : FShape) (g : Val) : Val := .lam
  (.app (.app (.val (travK .refX)) (.val (.lam (.app (.app (.val (selfF F)) (.val (g.shift 2 0)))
    (.var 0))))) (.var 0))

theorem foldImmV_subst (F : FShape) (g : Val) :
    Expr.subst 0 g (.val (.lam (.val (.lam
      (.app (.app (.val (travK .refX)) (.val (.lam (.app (.app (.val (selfF F)) (.var 3))
        (.var 0))))) (.var 0))))))
      = .val (foldCl F g) := by
  simp [foldCl, closed_subst (travK_closed _), closed_subst (selfF_closed F)]

theorem foldCl_subst (F : FShape) (g : Val) :
    Expr.subst 0 Val.unit (.val (.lam
      (.app (.app (.val (travK .refX)) (.val (.lam (.app (.app (.val (selfF F))
        (.val (g.shift 3 0))) (.var 0))))) (.var 0))))
      = .val (foldLam F g) := by
  simp [foldLam, closed_subst (travK_closed _), closed_subst (selfF_closed F), subst_shift_succ]

theorem foldLam_subst (F : FShape) (g w : Val) :
    Expr.subst 0 w (.app (.app (.val (travK .refX)) (.val (.lam (.app (.app (.val (selfF F))
        (.val (g.shift 2 0))) (.var 0))))) (.var 0))
      = .app (.app (.val (travK .refX)) (.val (hV F g))) (.val w) := by
  simp [hV, closed_subst (travK_closed _), closed_subst (selfF_closed F), subst_shift_succ]

/-- **The borrowed fold is sound.**  `foldImm : !U(∀'y ⊏ ⊤. A_R ⊸ F R) ⊸
!U(∀'y ⊏ @c. Imm 'y (μX. T) ⊸ F R)` at every `T` of the class `FShape` (closed leaves, `Ref X`,
guarded `X`, under `⊗`/`⊕`), at a result type `R` that outlives every lifetime, with `'y` free
in neither `μX. T` nor `R`. -/
theorem foldImm_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (F : FShape) (hF : F.WF) (hG : F.Guarded)
    (y : LifeVar) (c : Lifetime.Life) (R : VTy) (hΓ : Ctx.DeadP Γ)
    (hyM : ¬ VFree y (.mu F.ty)) (hyR : ¬ VFree y R) (hR : ∀ Δ a, VOutlives Δ a R) :
    SemV Δ Γ (.val (foldImmV F)) (.lolli (algTy F y R) (foldTy F y c R)) := by
  intro δ γ ls ρ _ hg₀
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg₀).2
  subst hρ
  rw [substAll_closed (foldImmV_closed F)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ g ρ₁ τ₀ hv₁ hcomp
  have hρ₁ : ρ₁ = PMap.empty := hv₁.1
  subst hρ₁
  have hg : ∀ ls, vC true (algTy F y R) ls δ g PMap.empty := fun ls' =>
    vC_local true _ (ext_empty ls₁ ls') hv₁
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_lolli _ _ g _ _ ?_
  rw [foldImmV_subst]
  refine wpTS_val _ _ _ _ ⟨rfl, ?_⟩
  rintro ls₂ - α ρa ρb ⟨hρa, -⟩ hc
  subst hρa
  have hρb := eq_of_compS_empty_left hc
  subst hρb
  refine wpTS_lolli _ _ Val.unit _ _ ?_
  rw [foldCl_subst]
  refine wpTS_val _ _ _ _ ?_
  intro ls₃ _ v ρ₃ τ hv hc₃
  rw [eq_of_compS_empty_left hc₃]
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, v = Val.loc ℓ := by
    obtain ⟨α₀, -, ℓ, hs₁⟩ := hv
    exact ⟨ℓ, (pure_sep_iff.mp hs₁).1.1⟩
  refine wpTS_lolli _ _ _ _ _ ?_
  rw [foldLam_subst]
  refine travK_app _ _ _ ls₃ _ ρ₃ ?_
  rw [tB_refX]
  obtain ⟨n, hn⟩ := witLt_exists hv
  exact wpTS_mono (fun ls' v ρ' hv' => (vP_ext hyR).mpr hv') ρ₃
    (pSpec_all hF hG hyM hyR hR hg n α ℓ ρ₃ ls₃ hv hn)

end BoCa.Fig16.LogRel.Core

end
