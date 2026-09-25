import Core.FoldImm

/-!
# Core — the owned fold as a typing rule

`foldOwn : !U(A′_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)` for `T` in the class `FShape`, consuming the
structure.  `A′_R = T.resO R` is `T` with `R` at every recursive position: at `Ref X` the fold
frees the cell and recurses on its content, at head `X` it recurses on the value.

The term is closed and generated from the shape (`travO`, `foldOwnV`), recursion by the Z
combinator.  `foldOwn_compatX` is its semantic typing, by induction on a bound of the owned
resource's size (`dsize`, as `mapInc`), and inside it on the size of the value (head `X`).  `R`
is any value type.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Types -/

/-- `A′_R`: `T` with `R` at every recursive position. -/
def FShape.resO (R : VTy) : FShape → VTy
  | .leaf A => A
  | .refX => R
  | .varX => R
  | .tensor F G => .tensor (F.resO R) (G.resO R)
  | .sum F G => .sum (F.resO R) (G.resO R)

/-- The algebra's type, `!U(A′_R ⊸ F R)`. -/
abbrev algOTy (F : FShape) (R : VTy) : VTy := .bang (VTy.lolli (F.resO R) R)

/-- The fold's type, `!U(μX. T ⊸ F R)`. -/
abbrev foldOTy (F : FShape) (R : VTy) : VTy := .bang (VTy.lolli (.mu F.ty) R)

/-! ### The term -/

/-- The body of `travO G` under its two binders (`h` = 1, `w` = 0): at a leaf `w`; at `Ref X`
`h (free w)`; at `X` `h w`; at `⊗` and `⊕` componentwise. -/
def travO : FShape → Val
  | .leaf _ => .lam (.val (.lam (.var 0)))
  | .refX => .lam (.val (.lam (.app (.var 1) (.app (.val (.prim .free)) (.var 0)))))
  | .varX => .lam (.val (.lam (.app (.var 1) (.var 0))))
  | .tensor F G => .lam (.val (.lam (.letpair (.var 0)
      (bindE (.app (.app (.val (travO F)) (.var 3)) (.var 1))
        (bindE (.app (.app (.val (travO G)) (.var 4)) (.var 1))
          (.pair (.var 1) (.var 0)))))))
  | .sum F G => .lam (.val (.lam (.case (.var 0)
      (bindE (.app (.app (.val (travO F)) (.var 2)) (.var 0)) (.inj₁ (.var 0)))
      (bindE (.app (.app (.val (travO G)) (.var 2)) (.var 0)) (.inj₂ (.var 0))))))

/-- The body of `travO G`. -/
def tO : FShape → Expr
  | .leaf _ => .var 0
  | .refX => .app (.var 1) (.app (.val (.prim .free)) (.var 0))
  | .varX => .app (.var 1) (.var 0)
  | .tensor F G => .letpair (.var 0)
      (bindE (.app (.app (.val (travO F)) (.var 3)) (.var 1))
        (bindE (.app (.app (.val (travO G)) (.var 4)) (.var 1))
          (.pair (.var 1) (.var 0))))
  | .sum F G => .case (.var 0)
      (bindE (.app (.app (.val (travO F)) (.var 2)) (.var 0)) (.inj₁ (.var 0)))
      (bindE (.app (.app (.val (travO G)) (.var 2)) (.var 0)) (.inj₂ (.var 0)))

theorem travO_eq (G : FShape) : travO G = .lam (.val (.lam (tO G))) := by cases G <;> rfl

theorem travO_closed : ∀ F : FShape, closedAt 0 (travO F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travO, bindE, closedAt, closedAt_mono _ (travO_closed F) (Nat.zero_le _),
        closedAt_mono _ (travO_closed G) (Nat.zero_le _)]
  | .sum F G => by
      simp [travO, bindE, closedAt, closedAt_mono _ (travO_closed F) (Nat.zero_le _),
        closedAt_mono _ (travO_closed G) (Nat.zero_le _)]

/-- The body of `fold = Z (λself. λg. λu. travO T (λw. self g w) u to r. g r)`. -/
def fBO (F : FShape) : Expr := .val (.lam (bindE
  (.app (.app (.val (travO F)) (.val (.lam (.app (.app (.var 3) (.var 2)) (.var 0))))) (.var 0))
  (.app (.var 2) (.var 0))))

theorem fBO_closed (F : FShape) : closedAt 2 (fBO F) = true := by
  simp [fBO, bindE, closedAt, closedAt_mono _ (travO_closed F) (Nat.zero_le _)]

/-- The recursive handle. -/
abbrev selfO (F : FShape) : Val := selfV (fBO F)

theorem selfO_closed (F : FShape) : closedAt 0 (selfO F).1 = true := selfV_closed (fBO_closed F)

/-- `λw. self g w`. -/
def hO (F : FShape) (g : Val) : Val := .lam (.app (.app (.val (selfO F)) (.val (g.shift 1 0))) (.var 0))

/-- **`foldOwn = λg. λw. self g w`**, a closed value. -/
def foldOwnV (F : FShape) : Val := .lam (.val (.lam (.app (.app (.val (selfO F)) (.var 1)) (.var 0))))

theorem foldOwnV_closed (F : FShape) : closedAt 0 (foldOwnV F).1 = true := by
  simp [foldOwnV, closedAt, closedAt_mono _ (selfO_closed F) (Nat.zero_le _)]

/-! ### Reduction -/

theorem travO_app (G : FShape) (h w : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (((tO G).subst 1 (h.shift 1 0)).subst 0 w) Q)
      (wpTS ls (.app (.app (.val (travO G)) (.val h)) (.val w)) Q) := by
  intro ρ hw
  rw [travO_eq]
  refine wpTS_beta_in (.appL .hole w) _ h ls Q ρ ?_
  exact wpTS_lolli ls _ w Q ρ hw

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

theorem tO_leaf (A : VTy) (h w : Val) :
    ((tO (.leaf A)).subst 1 (h.shift 1 0)).subst 0 w = .val w := by simp [tO]

theorem tO_refX (h w : Val) :
    ((tO .refX).subst 1 (h.shift 1 0)).subst 0 w
      = (Kont.appR (.val h) .hole).plug (.app (.val (.prim .free)) (.val w)) := by
  simp [tO, Kont.plug, subst_shift_succ]

theorem tO_varX (h w : Val) :
    ((tO .varX).subst 1 (h.shift 1 0)).subst 0 w = .app (.val h) (.val w) := by
  simp [tO, subst_shift_succ]

theorem tO_tensor (F G : FShape) (h v₁ v₂ : Val) :
    ((((tO (.tensor F G)).subst 1 (h.shift 1 0)).subst 0 (Val.pair v₁ v₂)))
      = .letpair (.val (Val.pair v₁ v₂))
          (bindE (.app (.app (.val (travO F)) (.val (h.shift 2 0))) (.var 1))
            (bindE (.app (.app (.val (travO G)) (.val (h.shift 3 0))) (.var 1))
              (.pair (.var 1) (.var 0)))) := by
  simp [tO, bindE, closed_subst (travO_closed _), subst_shift_succ]

theorem tensorO_body (F G : FShape) (h v₁ v₂ : Val) :
    ((bindE (.app (.app (.val (travO F)) (.val (h.shift 2 0))) (.var 1))
        (bindE (.app (.app (.val (travO G)) (.val (h.shift 3 0))) (.var 1))
          (.pair (.var 1) (.var 0)))).subst 0 (v₂.shift 1 0)).subst 0 v₁
      = (Kont.appR (.val (.lam (bindE (.app (.app (.val (travO G)) (.val (h.shift 1 0)))
          (.val (v₂.shift 1 0))) (.pair (.var 1) (.var 0))))) .hole).plug
          (.app (.app (.val (travO F)) (.val h)) (.val v₁)) := by
  simp [bindE, Kont.plug, closed_subst (travO_closed _), subst_shift_succ]

theorem tensorO_body₂ (G : FShape) (h v₂ r₁ : Val) :
    (bindE (.app (.app (.val (travO G)) (.val (h.shift 1 0))) (.val (v₂.shift 1 0)))
        (.pair (.var 1) (.var 0))).subst 0 r₁
      = (Kont.appR (.val (.lam (.pair (.val (r₁.shift 1 0)) (.var 0)))) .hole).plug
          (.app (.app (.val (travO G)) (.val h)) (.val v₂)) := by
  simp [bindE, Kont.plug, closed_subst (travO_closed _), subst_shift_succ]

theorem tO_sum (F G : FShape) (h w : Val) :
    ((tO (.sum F G)).subst 1 (h.shift 1 0)).subst 0 w
      = .case (.val w)
          (bindE (.app (.app (.val (travO F)) (.val (h.shift 1 0))) (.var 0)) (.inj₁ (.var 0)))
          (bindE (.app (.app (.val (travO G)) (.val (h.shift 1 0))) (.var 0)) (.inj₂ (.var 0))) := by
  simp [tO, bindE, closed_subst (travO_closed _), subst_shift_succ]

theorem sumO_branch (F : FShape) (h v : Val) (inj : Expr → Expr)
    (hinj : ∀ j s e, Expr.subst j s (inj e) = inj (Expr.subst j s e)) :
    (bindE (.app (.app (.val (travO F)) (.val (h.shift 1 0))) (.var 0)) (inj (.var 0))).subst 0 v
      = (Kont.appR (.val (.lam (inj (.var 0)))) .hole).plug
          (.app (.app (.val (travO F)) (.val h)) (.val v)) := by
  simp [bindE, Kont.plug, closed_subst (travO_closed _), subst_shift_succ, hinj]

theorem fBO_subst (F : FShape) {S : Val} (hS : closedAt 0 S.1 = true) (g w : Val) :
    (Kont.appL .hole w).plug (((fBO F).subst 1 S).subst 0 g)
      = .app (.val (.lam (bindE (.app (.app (.val (travO F))
          (.val (.lam (.app (.app (.val S) (.val (g.shift 2 0))) (.var 0))))) (.var 0))
          (.app (.val (g.shift 2 0)) (.var 0))))) (.val w) := by
  simp [Kont.plug, fBO, bindE, closed_subst (travO_closed _), closed_subst hS, closed_shift hS]

theorem fBO_body (F : FShape) {S : Val} (hS : closedAt 0 S.1 = true) (g w : Val) :
    (bindE (.app (.app (.val (travO F))
          (.val (.lam (.app (.app (.val S) (.val (g.shift 2 0))) (.var 0))))) (.var 0))
          (.app (.val (g.shift 2 0)) (.var 0))).subst 0 w
      = (Kont.appR (.val (.lam (.app (.val (g.shift 1 0)) (.var 0)))) .hole).plug
          (.app (.app (.val (travO F)) (.val (.lam (.app (.app (.val S) (.val (g.shift 1 0)))
            (.var 0))))) (.val w)) := by
  simp [Kont.plug, bindE, closed_subst (travO_closed _), closed_subst hS, subst_shift_succ]

/-- `h w` for `h = λw. self g w` reaches `travO T h w to r. g r`. -/
theorem hO_app (F : FShape) (g w : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls ((Kont.appR (.val (.lam (.app (.val (g.shift 1 0)) (.var 0)))) .hole).plug
        (.app (.app (.val (travO F)) (.val (hO F g))) (.val w))) Q)
      (wpTS ls (.app (.val (hO F g)) (.val w)) Q) := by
  intro ρ hw
  refine wpTS_lolli _ _ w Q ρ ?_
  have e₁ : Expr.subst 0 w (.app (.app (.val (selfO F)) (.val (g.shift 1 0))) (.var 0))
      = .app (.app (.val (selfO F)) (.val g)) (.val w) := by
    simp [closed_subst (selfO_closed F), subst_shift_succ]
  rw [e₁]
  refine wpTS_selfV_in (fBO_closed F) (.appL .hole w) g ls Q ρ ?_
  rw [fixV_eq (fBO_closed F)]
  refine wpTS_beta_in (.appL .hole w) _ g ls Q ρ ?_
  rw [fBO_subst F (selfO_closed F)]
  refine wpTS_lolli _ _ w Q ρ ?_
  rw [fBO_body F (selfO_closed F)]
  exact hw

theorem algO_subst (g r : Val) :
    Expr.subst 0 r (.app (.val (g.shift 1 0)) (.var 0)) = .app (.val g) (.val r) := by
  simp [subst_shift_succ]

theorem foldOwnV_subst (F : FShape) (g : Val) :
    Expr.subst 0 g (.val (.lam (.app (.app (.val (selfO F)) (.var 1)) (.var 0))))
      = .val (hO F g) := by
  simp [hO, closed_subst (selfO_closed F)]

/-! ### The traversal -/

theorem dsize_le_left {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) : dsize ρ₁ ≤ dsize ρ := by
  classical
  refine Finset.card_le_card (fun m hm => ?_)
  obtain ⟨ψ, e⟩ := Option.ne_none_iff_exists'.mp (mem_rdom.mp hm)
  obtain ⟨ψ', e', -⟩ := compS_get_left' h e
  exact mem_rdom.mpr (by rw [e']; simp)

theorem dsize_le_right {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) : dsize ρ₂ ≤ dsize ρ :=
  dsize_le_left (ResU.CompS.comm h)

/-- The recursive call on a value of `M` whose resource has at most `n` cells, smaller than
`K`. -/
def HOSpec (M R : VTy) (δ : LSub) (n K : Nat) (h : Val) : Prop :=
  ∀ w χ ls, sizeOf w.1 < K → vP M ls δ w χ → dsize χ ≤ n →
    wpTS ls (.app (.val h) (.val w)) (fun ls' v => vP R ls' δ v) χ

/-- **The owned traversal.**  At a sub-shape `G`, `travO G h w` takes `w : G[M/X]` to a value
of `G.resO R`, given the recursive call on a value of fewer cells (`hP`, through a freed
`Ref`) and on a smaller value (`hH`, at a head `X`). -/
theorem travO_spec {M R : VTy} {δ : LSub} {n K : Nat} {h : Val}
    (hP : ∀ w ρ ls, vP M ls δ w ρ → dsize ρ < n →
      wpTS ls (.app (.val h) (.val w)) (fun ls' v => vP R ls' δ v) ρ)
    (hH : HOSpec M R δ n K h) :
    ∀ (G : FShape), G.WF → ∀ w χ ls, sizeOf w.1 ≤ K → (G = .varX → sizeOf w.1 < K) →
      vP (VTy.inst M G.ty) ls δ w χ → dsize χ ≤ n →
      wpTS ls (.app (.app (.val (travO G)) (.val h)) (.val w))
        (fun ls' r => vP (G.resO R) ls' δ r) χ
  | .leaf A, hA, w, χ, ls, _, _, hv, _ => by
      refine travO_app _ h w ls _ χ ?_
      rw [tO_leaf]
      have e : VTy.inst M A = A := VTy.subst_closed0 hA _
      simp only [FShape.ty, e] at hv
      exact wpTS_val ls w _ χ hv
  | .refX, _, w, χ, ls, _, _, hv, hn => by
      refine travO_app _ h w ls _ χ ?_
      rw [tO_refX]
      change vP (.ref M) ls δ w χ at hv
      obtain ⟨ℓ, v', hs⟩ := hv
      obtain ⟨rfl, ρa, ρb, hc, hown, hM⟩ := pure_sep_iff.mp hs
      refine wpTS_bind _ _ ls _ χ ?_
      refine wpTS_free ls ℓ v' _ χ ⟨ρa, ρb, hc, hown, ?_⟩
      simp only [Kont.plug]
      rw [hown] at hc
      exact hP v' ρb ls hM
        (lt_of_lt_of_le (dsize_tail_lt hc ⟨PMap.empty, ResU.comp_empty_right _⟩) hn)
  | .varX, _, w, χ, ls, _, hlt, hv, hn => by
      refine travO_app _ h w ls _ χ ?_
      rw [tO_varX]
      exact hH w χ ls (hlt rfl) hv hn
  | .tensor F G, hFG, w, χ, ls, hK, _, hv, hn => by
      obtain ⟨v₁, v₂, hs⟩ := hv
      obtain ⟨hw, χ₁, χ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      subst hw
      have hs₁ : sizeOf v₁.1 < K := by rw [sizeOf_pair] at hK; omega
      have hs₂ : sizeOf v₂.1 < K := by rw [sizeOf_pair] at hK; omega
      refine travO_app _ h _ ls _ χ ?_
      rw [tO_tensor]
      refine wpTS_tensor ls v₁ v₂ _ _ χ ?_
      rw [tensorO_body]
      refine wpTS_bind_frame _ _ ls (fun ls' r => vP (F.resO R) ls' δ r)
        (fun ls' ρ => vP (VTy.inst M G.ty) ls' δ v₂ ρ ∧ dsize ρ ≤ n)
        _ (fun ls' hls ρ hρ => ⟨vP_same hls hρ.1, hρ.2⟩) ?_ χ
        ⟨χ₁, χ₂, hc, travO_spec hP hH F hFG.1 v₁ χ₁ ls (le_of_lt hs₁) (fun _ => hs₁) h₁
          (le_trans (dsize_le_left hc) hn), h₂, le_trans (dsize_le_right hc) hn⟩
      rintro ls' hls r₁ σ ⟨σ₁, σ₂, hcσ, hr₁, hv₂, hn₂⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ r₁ _ σ ?_
      rw [tensorO_body₂]
      refine wpTS_bind_frame _ _ ls' (fun ls'' r => vP (G.resO R) ls'' δ r)
        (fun ls'' => vP (F.resO R) ls'' δ r₁)
        _ (fun ls'' hls' ρ hρ => vP_same hls' hρ) ?_ σ
        ⟨σ₂, σ₁, ResU.CompS.comm hcσ, travO_spec hP hH G hFG.2 v₂ σ₂ ls' (le_of_lt hs₂)
          (fun _ => hs₂) hv₂ hn₂, hr₁⟩
      rintro ls'' - r₂ τ ⟨τ₁, τ₂, hcτ, hr₂, hr₁'⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ r₂ _ τ ?_
      rw [tensor_body₃]
      exact wpTS_val ls'' _ _ τ ⟨r₁, r₂, pure_sep_iff.mpr ⟨rfl, τ₂, τ₁, ResU.CompS.comm hcτ, hr₁', hr₂⟩⟩
  | .sum F G, hFG, w, χ, ls, hK, _, hv, hn => by
      rcases hv with ⟨v, hs⟩ | ⟨v, hs⟩
      · obtain ⟨hw, hv⟩ := pure_sep_iff.mp hs
        subst hw
        have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₁ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine travO_app _ h _ ls _ χ ?_
        rw [tO_sum]
        refine wpTS_sum₁ ls v _ _ _ χ ?_
        rw [sumO_branch F h v Expr.inj₁ (fun _ _ _ => rfl)]
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (travO_spec hP hH F hFG.1 v χ ls (le_of_lt hsz) (fun _ => hsz) hv hn)
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        exact wpTS_val ls' (Val.inj₁ r) _ ρ (Or.inl ⟨r, pure_sep_iff.mpr ⟨rfl, hr⟩⟩)
      · obtain ⟨hw, hv⟩ := pure_sep_iff.mp hs
        subst hw
        have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₂ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine travO_app _ h _ ls _ χ ?_
        rw [tO_sum]
        refine wpTS_sum₂ ls v _ _ _ χ ?_
        rw [sumO_branch G h v Expr.inj₂ (fun _ _ _ => rfl)]
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (travO_spec hP hH G hFG.2 v χ ls (le_of_lt hsz) (fun _ => hsz) hv hn)
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        exact wpTS_val ls' (Val.inj₂ r) _ ρ (Or.inr ⟨r, pure_sep_iff.mpr ⟨rfl, hr⟩⟩)

/-! ### Induction on the resource size, then on the value -/

/-- **The recursive call**, at every resource bound `n` and value bound `K`. -/
theorem hOSpec_all {F : FShape} (hF : F.WF) (hG : F.Guarded) {R : VTy} {δ : LSub} {g : Val}
    (hg : ∀ ls, vC true (algOTy F R) ls δ g PMap.empty) :
    ∀ n K, HOSpec (.mu F.ty) R δ n K (hO F g) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    have hP : ∀ w ρ ls, vP (.mu F.ty) ls δ w ρ → dsize ρ < n →
        wpTS ls (.app (.val (hO F g)) (.val w)) (fun ls' v => vP R ls' δ v) ρ :=
      fun w ρ ls hv hlt => ihn (dsize ρ) hlt (sizeOf w.1 + 1) w ρ ls (Nat.lt_succ_self _) hv le_rfl
    intro K
    induction K with
    | zero => intro w χ ls hlt; exact absurd hlt (Nat.not_lt_zero _)
    | succ K ihK =>
        intro w χ ls hlt hv hn
        refine hO_app F g w ls _ χ ?_
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (travO_spec hP ihK F hF w χ ls (Nat.lt_succ_iff.mp hlt)
            (fun e => by subst e; exact hG.elim) (vC_unfold hv).2.2 hn)
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        rw [algO_subst]
        obtain ⟨-, hthunk⟩ := hg ls'
        exact hthunk ls' (Ext.refl _ _) r ρ ρ hr (ResU.CompS.comm (ResU.comp_empty_right ρ))

/-! ### The rule -/

/-- **The owned fold is sound.**  `foldOwn : !U(A′_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)` at every `T`
of the class `FShape` and every `R`. -/
theorem foldOwn_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (F : FShape) (hF : F.WF) (hG : F.Guarded)
    (R : VTy) (hΓ : Ctx.Dead Γ) :
    SemV Δ Γ (.val (foldOwnV F)) (.lolli (algOTy F R) (foldOTy F R)) := by
  intro δ γ ls ρ _ hg₀
  have hρ : ρ = PMap.empty := gSepC_dead hΓ (gDenC_iff.mp hg₀).2
  subst hρ
  rw [substAll_closed (foldOwnV_closed F)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ g ρ₁ τ₀ hv₁ hcomp
  have hρ₁ : ρ₁ = PMap.empty := hv₁.1
  subst hρ₁
  have hg : ∀ ls, vC true (algOTy F R) ls δ g PMap.empty := fun ls' =>
    vC_local true _ (ext_empty ls₁ ls') hv₁
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_lolli _ _ g _ _ ?_
  rw [foldOwnV_subst]
  refine wpTS_val _ _ _ _ ⟨rfl, ?_⟩
  intro ls₂ _ v ρ₂ τ hv hc
  rw [eq_of_compS_empty_left hc]
  exact hOSpec_all hF hG hg (dsize ρ₂) (sizeOf v.1 + 1) v ρ₂ ls₂ (Nat.lt_succ_self _) hv le_rfl

end BoCa.Fig16.LogRel.Core

end
