import CBPVMu.FoldOwn

/-!
# CBPVMu — the owned fold with reuse

`foldReuse : !U(A″_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)` for `T` in the class `FShape`, consuming the
structure and handing its cells to the algebra.  `A″_R = T.resR R` is `T` with `R` at a head
`X` and `Ref 1 ⊗ R` at every `Ref X`: at `Ref X` the fold empties the cell by `swap w ()`,
recurses on the content, and passes the emptied cell (a `Ref 1`, the reuse token) with the
result.  The algebra refills the cell with `swap`, whose type `Ref A ⊸ B ⊸ Ref B ⊗ A` changes
the cell's content type, so a rebuilt node lives at the location of the consumed one.  No type
former is added: the token is an owned `Ref 1`.

The term is `FoldOwn.lean`'s with the `Ref X` clause replaced (`travR`, `foldReuseV`).
`foldReuse_compatX` is its semantic typing, by the same induction on a bound of the owned
resource's size, here through the emptied cell (`dsize_tail_lt` at the cell before the swap).

* `wpTS_swap`: `swap ℓ v` at an owned cell, as a `wpTS` rule (6.169's steps).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVMu
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### `swap` at an owned cell -/

/-- **`swap ℓ v`** at `ℓ ↦ w` returns `(ℓ, w)` with `ℓ ↦ v`: 6.169's steps (`wp⊸`, `wp-load`,
`wp-store`, `wp1`, `wp-val`) as a rule. -/
theorem wpTS_swap (ls : List SRec) (ℓ : Loc) (w v : Val) (Q : List SRec → Val → WProp) :
    Entails (sep (ptoOwn ℓ w) (wand (ptoOwn ℓ v) (Q ls (.pair (.loc ℓ) w))))
      (wpTS ls (.app (.app swap (.val (.loc ℓ))) (.val v)) Q) := by
  rintro ρ ⟨ρo, ρR, hc, rfl, hR⟩
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (elet (.app load' BoCa.v1)
          (.seq (.app (.app store' BoCa.v2) BoCa.v1) (.pair BoCa.v2 BoCa.v0)))))
      = Expr.val (Val.lam (elet (eLoad ℓ)
          (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                (.pair (.val (.loc ℓ)) BoCa.v0)))) := by
    simp [elet, eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, BoCa.v2, load', store']
  refine wpTS_beta_in (.appL .hole v) _ (Val.loc ℓ) ls Q _ ?_
  rw [hβ₁]
  simp only [Kont.plug]
  have hβ₂ : Expr.subst 0 v
        (elet (eLoad ℓ) (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                              (.pair (.val (.loc ℓ)) BoCa.v0)))
      = elet (eLoad ℓ) (.seq (eStore ℓ (v.shift 1 0)) (.pair (.val (.loc ℓ)) BoCa.v0)) := by
    simp [elet, eLoad, eStore, Expr.subst, BoCa.v0, BoCa.v1, store']
  refine wpTS_lolli _ _ v _ _ ?_
  rw [hβ₂]
  refine wpTS_bind (.appR (.val (.lam _)) .hole) (eLoad ℓ) ls _ _ ?_
  refine wpTS_load ls ℓ w _ _ ⟨_, ρR, hc, rfl, ?_⟩
  intro ρ' σ' hp' hc'
  subst hp'
  simp only [Kont.plug]
  have hβ₃ : Expr.subst 0 w
        (Expr.seq (eStore ℓ (v.shift 1 0)) (.pair (.val (.loc ℓ)) BoCa.v0))
      = Expr.seq (eStore ℓ v) (.pair (.val (.loc ℓ)) (.val w)) := by
    simp [eStore, Expr.subst, BoCa.v0,
      Expr.subst_shift 0 0 0 w v.val (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  refine wpTS_lolli _ _ w _ _ ?_
  rw [hβ₃]
  refine wpTS_bind (.seq .hole (.pair (.val (.loc ℓ)) (.val w))) (eStore ℓ v) ls _ _ ?_
  refine wpTS_store ls ℓ w v _ _ ⟨_, ρR, ResU.CompS.comm hc', rfl, ?_⟩
  intro ρ₃ σ₃ hp₃ hc₃
  simp only [Kont.plug]
  refine wpTS_1 _ _ _ _ ?_
  exact wpTS_val ls (.pair (.loc ℓ) w) _ _ (hR ρ₃ σ₃ hp₃ hc₃)

/-! ### Types -/

/-- `A″_R`: `T` with `R` at a head `X` and `Ref 1 ⊗ R` at every `Ref X`. -/
def FShape.resR (R : VTy) : FShape → VTy
  | .leaf A => A
  | .refX => .tensor (.ref .unit) R
  | .varX => R
  | .tensor F G => .tensor (F.resR R) (G.resR R)
  | .sum F G => .sum (F.resR R) (G.resR R)

/-- The algebra's type, `!U(A″_R ⊸ F R)`. -/
abbrev algRTy (F : FShape) (R : VTy) : VTy := .bang (VTy.lolli (F.resR R) R)

/-! ### The term -/

/-- The body of `travR G` under its two binders (`h` = 1, `w` = 0): at a leaf `w`; at `Ref X`
`swap w () to q. let (c, v) = q in h v to r. (c, r)`; at `X` `h w`; at `⊗` and `⊕`
componentwise. -/
def travR : FShape → Val
  | .leaf _ => .lam (.val (.lam (.var 0)))
  | .refX => .lam (.val (.lam (bindE (.app (.app swap (.var 0)) (.val .unit))
      (.letpair (.var 0) (bindE (.app (.var 4) (.var 0)) (.pair (.var 2) (.var 0)))))))
  | .varX => .lam (.val (.lam (.app (.var 1) (.var 0))))
  | .tensor F G => .lam (.val (.lam (.letpair (.var 0)
      (bindE (.app (.app (.val (travR F)) (.var 3)) (.var 1))
        (bindE (.app (.app (.val (travR G)) (.var 4)) (.var 1))
          (.pair (.var 1) (.var 0)))))))
  | .sum F G => .lam (.val (.lam (.case (.var 0)
      (bindE (.app (.app (.val (travR F)) (.var 2)) (.var 0)) (.inj₁ (.var 0)))
      (bindE (.app (.app (.val (travR G)) (.var 2)) (.var 0)) (.inj₂ (.var 0))))))

/-- The body of `travR G`. -/
def tR : FShape → Expr
  | .leaf _ => .var 0
  | .refX => bindE (.app (.app swap (.var 0)) (.val .unit))
      (.letpair (.var 0) (bindE (.app (.var 4) (.var 0)) (.pair (.var 2) (.var 0))))
  | .varX => .app (.var 1) (.var 0)
  | .tensor F G => .letpair (.var 0)
      (bindE (.app (.app (.val (travR F)) (.var 3)) (.var 1))
        (bindE (.app (.app (.val (travR G)) (.var 4)) (.var 1))
          (.pair (.var 1) (.var 0))))
  | .sum F G => .case (.var 0)
      (bindE (.app (.app (.val (travR F)) (.var 2)) (.var 0)) (.inj₁ (.var 0)))
      (bindE (.app (.app (.val (travR G)) (.var 2)) (.var 0)) (.inj₂ (.var 0)))

theorem travR_eq (G : FShape) : travR G = .lam (.val (.lam (tR G))) := by cases G <;> rfl

theorem travR_closed : ∀ F : FShape, closedAt 0 (travR F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travR, bindE, closedAt, closedAt_mono _ (travR_closed F) (Nat.zero_le _),
        closedAt_mono _ (travR_closed G) (Nat.zero_le _)]
  | .sum F G => by
      simp [travR, bindE, closedAt, closedAt_mono _ (travR_closed F) (Nat.zero_le _),
        closedAt_mono _ (travR_closed G) (Nat.zero_le _)]

/-- The body of `fold = Z (λself. λg. λu. travR T (λw. self g w) u to r. g r)`. -/
def fBR (F : FShape) : Expr := .val (.lam (bindE
  (.app (.app (.val (travR F)) (.val (.lam (.app (.app (.var 3) (.var 2)) (.var 0))))) (.var 0))
  (.app (.var 2) (.var 0))))

theorem fBR_closed (F : FShape) : closedAt 2 (fBR F) = true := by
  simp [fBR, bindE, closedAt, closedAt_mono _ (travR_closed F) (Nat.zero_le _)]

/-- The recursive handle. -/
abbrev selfR (F : FShape) : Val := selfV (fBR F)

theorem selfR_closed (F : FShape) : closedAt 0 (selfR F).1 = true := selfV_closed (fBR_closed F)

/-- `λw. self g w`. -/
def hR (F : FShape) (g : Val) : Val := .lam (.app (.app (.val (selfR F)) (.val (g.shift 1 0))) (.var 0))

/-- **`foldOwn = λg. λw. self g w`**, a closed value. -/
def foldReuseV (F : FShape) : Val := .lam (.val (.lam (.app (.app (.val (selfR F)) (.var 1)) (.var 0))))

theorem foldReuseV_closed (F : FShape) : closedAt 0 (foldReuseV F).1 = true := by
  simp [foldReuseV, closedAt, closedAt_mono _ (selfR_closed F) (Nat.zero_le _)]

/-! ### Reduction -/

theorem travR_app (G : FShape) (h w : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (((tR G).subst 1 (h.shift 1 0)).subst 0 w) Q)
      (wpTS ls (.app (.app (.val (travR G)) (.val h)) (.val w)) Q) := by
  intro ρ hw
  rw [travR_eq]
  refine wpTS_beta_in (.appL .hole w) _ h ls Q ρ ?_
  exact wpTS_lolli ls _ w Q ρ hw

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

theorem tR_leaf (A : VTy) (h w : Val) :
    ((tR (.leaf A)).subst 1 (h.shift 1 0)).subst 0 w = .val w := by simp [tR]

theorem swap_closed : closedAt 0 swap = true := rfl

theorem swap_subst (j : Nat) (s : Val) : Expr.subst j s swap = swap :=
  subst_closedAt swap s swap_closed (Nat.zero_le j)

theorem tR_refX (h w : Val) :
    ((tR .refX).subst 1 (h.shift 1 0)).subst 0 w
      = (Kont.appR (.val (.lam (.letpair (.var 0) (bindE (.app (.val (h.shift 3 0)) (.var 0))
          (.pair (.var 2) (.var 0)))))) .hole).plug (.app (.app swap (.val w)) (.val .unit)) := by
  simp [tR, bindE, Kont.plug, subst_shift_succ, swap_subst]

theorem refR_body (h v : Val) (ℓ : Loc) :
    (((bindE (.app (.val (h.shift 3 0)) (.var 0)) (.pair (.var 2) (.var 0))).subst 2
        ((Val.pair (.loc ℓ) v).shift 2 0)).subst 0 (v.shift 1 0)).subst 0 (.loc ℓ)
      = (Kont.appR (.val (.lam (.pair (.val (.loc ℓ)) (.var 0)))) .hole).plug
          (.app (.val h) (.val v)) := by
  simp [bindE, Kont.plug, subst_shift_succ, Expr.shift]

theorem tR_varX (h w : Val) :
    ((tR .varX).subst 1 (h.shift 1 0)).subst 0 w = .app (.val h) (.val w) := by
  simp [tR, subst_shift_succ]

theorem tR_tensor (F G : FShape) (h v₁ v₂ : Val) :
    ((((tR (.tensor F G)).subst 1 (h.shift 1 0)).subst 0 (Val.pair v₁ v₂)))
      = .letpair (.val (Val.pair v₁ v₂))
          (bindE (.app (.app (.val (travR F)) (.val (h.shift 2 0))) (.var 1))
            (bindE (.app (.app (.val (travR G)) (.val (h.shift 3 0))) (.var 1))
              (.pair (.var 1) (.var 0)))) := by
  simp [tR, bindE, closed_subst (travR_closed _), subst_shift_succ]

theorem tensorR_body (F G : FShape) (h v₁ v₂ : Val) :
    ((bindE (.app (.app (.val (travR F)) (.val (h.shift 2 0))) (.var 1))
        (bindE (.app (.app (.val (travR G)) (.val (h.shift 3 0))) (.var 1))
          (.pair (.var 1) (.var 0)))).subst 0 (v₂.shift 1 0)).subst 0 v₁
      = (Kont.appR (.val (.lam (bindE (.app (.app (.val (travR G)) (.val (h.shift 1 0)))
          (.val (v₂.shift 1 0))) (.pair (.var 1) (.var 0))))) .hole).plug
          (.app (.app (.val (travR F)) (.val h)) (.val v₁)) := by
  simp [bindE, Kont.plug, closed_subst (travR_closed _), subst_shift_succ]

theorem tensorR_body₂ (G : FShape) (h v₂ r₁ : Val) :
    (bindE (.app (.app (.val (travR G)) (.val (h.shift 1 0))) (.val (v₂.shift 1 0)))
        (.pair (.var 1) (.var 0))).subst 0 r₁
      = (Kont.appR (.val (.lam (.pair (.val (r₁.shift 1 0)) (.var 0)))) .hole).plug
          (.app (.app (.val (travR G)) (.val h)) (.val v₂)) := by
  simp [bindE, Kont.plug, closed_subst (travR_closed _), subst_shift_succ]

theorem tR_sum (F G : FShape) (h w : Val) :
    ((tR (.sum F G)).subst 1 (h.shift 1 0)).subst 0 w
      = .case (.val w)
          (bindE (.app (.app (.val (travR F)) (.val (h.shift 1 0))) (.var 0)) (.inj₁ (.var 0)))
          (bindE (.app (.app (.val (travR G)) (.val (h.shift 1 0))) (.var 0)) (.inj₂ (.var 0))) := by
  simp [tR, bindE, closed_subst (travR_closed _), subst_shift_succ]

theorem sumR_branch (F : FShape) (h v : Val) (inj : Expr → Expr)
    (hinj : ∀ j s e, Expr.subst j s (inj e) = inj (Expr.subst j s e)) :
    (bindE (.app (.app (.val (travR F)) (.val (h.shift 1 0))) (.var 0)) (inj (.var 0))).subst 0 v
      = (Kont.appR (.val (.lam (inj (.var 0)))) .hole).plug
          (.app (.app (.val (travR F)) (.val h)) (.val v)) := by
  simp [bindE, Kont.plug, closed_subst (travR_closed _), subst_shift_succ, hinj]

theorem fBR_subst (F : FShape) {S : Val} (hS : closedAt 0 S.1 = true) (g w : Val) :
    (Kont.appL .hole w).plug (((fBR F).subst 1 S).subst 0 g)
      = .app (.val (.lam (bindE (.app (.app (.val (travR F))
          (.val (.lam (.app (.app (.val S) (.val (g.shift 2 0))) (.var 0))))) (.var 0))
          (.app (.val (g.shift 2 0)) (.var 0))))) (.val w) := by
  simp [Kont.plug, fBR, bindE, closed_subst (travR_closed _), closed_subst hS, closed_shift hS]

theorem fBR_body (F : FShape) {S : Val} (hS : closedAt 0 S.1 = true) (g w : Val) :
    (bindE (.app (.app (.val (travR F))
          (.val (.lam (.app (.app (.val S) (.val (g.shift 2 0))) (.var 0))))) (.var 0))
          (.app (.val (g.shift 2 0)) (.var 0))).subst 0 w
      = (Kont.appR (.val (.lam (.app (.val (g.shift 1 0)) (.var 0)))) .hole).plug
          (.app (.app (.val (travR F)) (.val (.lam (.app (.app (.val S) (.val (g.shift 1 0)))
            (.var 0))))) (.val w)) := by
  simp [Kont.plug, bindE, closed_subst (travR_closed _), closed_subst hS, subst_shift_succ]

/-- `h w` for `h = λw. self g w` reaches `travR T h w to r. g r`. -/
theorem hR_app (F : FShape) (g w : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls ((Kont.appR (.val (.lam (.app (.val (g.shift 1 0)) (.var 0)))) .hole).plug
        (.app (.app (.val (travR F)) (.val (hR F g))) (.val w))) Q)
      (wpTS ls (.app (.val (hR F g)) (.val w)) Q) := by
  intro ρ hw
  refine wpTS_lolli _ _ w Q ρ ?_
  have e₁ : Expr.subst 0 w (.app (.app (.val (selfR F)) (.val (g.shift 1 0))) (.var 0))
      = .app (.app (.val (selfR F)) (.val g)) (.val w) := by
    simp [closed_subst (selfR_closed F), subst_shift_succ]
  rw [e₁]
  refine wpTS_selfV_in (fBR_closed F) (.appL .hole w) g ls Q ρ ?_
  rw [fixV_eq (fBR_closed F)]
  refine wpTS_beta_in (.appL .hole w) _ g ls Q ρ ?_
  rw [fBR_subst F (selfR_closed F)]
  refine wpTS_lolli _ _ w Q ρ ?_
  rw [fBR_body F (selfR_closed F)]
  exact hw

theorem algR_subst (g r : Val) :
    Expr.subst 0 r (.app (.val (g.shift 1 0)) (.var 0)) = .app (.val g) (.val r) := by
  simp [subst_shift_succ]

theorem foldReuseV_subst (F : FShape) (g : Val) :
    Expr.subst 0 g (.val (.lam (.app (.app (.val (selfR F)) (.var 1)) (.var 0))))
      = .val (hR F g) := by
  simp [hR, closed_subst (selfR_closed F)]

/-! ### The traversal -/

/-- The recursive call on a value of `M` whose resource has at most `n` cells, smaller than
`K`. -/
def HRSpec (M R : VTy) (δ : LSub) (n K : Nat) (h : Val) : Prop :=
  ∀ w χ ls, sizeOf w.1 < K → vP M ls δ w χ → dsize χ ≤ n →
    wpTS ls (.app (.val h) (.val w)) (fun ls' v => vP R ls' δ v) χ

/-- **The owned traversal.**  At a sub-shape `G`, `travR G h w` takes `w : G[M/X]` to a value
of `G.resR R`, given the recursive call on a value of fewer cells (`hP`, through a freed
`Ref`) and on a smaller value (`hH`, at a head `X`). -/
theorem travR_spec {M R : VTy} {δ : LSub} {n K : Nat} {h : Val}
    (hP : ∀ w ρ ls, vP M ls δ w ρ → dsize ρ < n →
      wpTS ls (.app (.val h) (.val w)) (fun ls' v => vP R ls' δ v) ρ)
    (hH : HRSpec M R δ n K h) :
    ∀ (G : FShape), G.WF → ∀ w χ ls, sizeOf w.1 ≤ K → (G = .varX → sizeOf w.1 < K) →
      vP (VTy.inst M G.ty) ls δ w χ → dsize χ ≤ n →
      wpTS ls (.app (.app (.val (travR G)) (.val h)) (.val w))
        (fun ls' r => vP (G.resR R) ls' δ r) χ
  | .leaf A, hA, w, χ, ls, _, _, hv, _ => by
      refine travR_app _ h w ls _ χ ?_
      rw [tR_leaf]
      have e : VTy.inst M A = A := VTy.subst_closed0 hA _
      simp only [FShape.ty, e] at hv
      exact wpTS_val ls w _ χ hv
  | .refX, _, w, χ, ls, _, _, hv, hn => by
      refine travR_app _ h w ls _ χ ?_
      rw [tR_refX]
      change vP (.ref M) ls δ w χ at hv
      obtain ⟨ℓ, v', hs⟩ := hv
      obtain ⟨rfl, ρa, ρb, hc, hown, hM⟩ := pure_sep_iff.mp hs
      have hlt : dsize ρb < n := by
        have hc' := hc
        rw [hown] at hc'
        exact lt_of_lt_of_le (dsize_tail_lt hc' ⟨PMap.empty, ResU.comp_empty_right _⟩) hn
      refine wpTS_bind _ _ ls _ χ ?_
      refine wpTS_swap ls ℓ v' .unit _ χ ⟨ρa, ρb, hc, hown, ?_⟩
      intro σa σ hσa hcσ
      simp only [Kont.plug]
      refine wpTS_lolli _ _ _ _ _ ?_
      refine wpTS_tensor ls (.loc ℓ) v' _ _ σ ?_
      rw [refR_body]
      refine wpTS_bind_frame _ _ ls (fun ls' r => vP R ls' δ r) (fun _ => ptoOwn ℓ .unit) _
        (fun _ _ _ h => h) ?_ σ ⟨ρb, σa, hcσ, hP v' ρb ls hM hlt, hσa⟩
      rintro ls' - r τ ⟨τ₁, τ₂, hcτ, hr, hτ₂⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ r _ τ ?_
      have e : (Expr.pair (.val (Val.loc ℓ)) (.var 0)).subst 0 r = .val (Val.pair (.loc ℓ) r) := by
        simp
      rw [e]
      exact wpTS_val ls' _ _ τ ⟨.loc ℓ, r, pure_sep_iff.mpr ⟨rfl, τ₂, τ₁, ResU.CompS.comm hcτ,
        ⟨ℓ, .unit, pure_sep_iff.mpr ⟨rfl, τ₂, PMap.empty, ResU.comp_empty_right _, hτ₂,
          rfl, rfl⟩⟩, hr⟩⟩
  | .varX, _, w, χ, ls, _, hlt, hv, hn => by
      refine travR_app _ h w ls _ χ ?_
      rw [tR_varX]
      exact hH w χ ls (hlt rfl) hv hn
  | .tensor F G, hFG, w, χ, ls, hK, _, hv, hn => by
      obtain ⟨v₁, v₂, hs⟩ := hv
      obtain ⟨hw, χ₁, χ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      subst hw
      have hs₁ : sizeOf v₁.1 < K := by rw [sizeOf_pair] at hK; omega
      have hs₂ : sizeOf v₂.1 < K := by rw [sizeOf_pair] at hK; omega
      refine travR_app _ h _ ls _ χ ?_
      rw [tR_tensor]
      refine wpTS_tensor ls v₁ v₂ _ _ χ ?_
      rw [tensorR_body]
      refine wpTS_bind_frame _ _ ls (fun ls' r => vP (F.resR R) ls' δ r)
        (fun ls' ρ => vP (VTy.inst M G.ty) ls' δ v₂ ρ ∧ dsize ρ ≤ n)
        _ (fun ls' hls ρ hρ => ⟨vP_same hls hρ.1, hρ.2⟩) ?_ χ
        ⟨χ₁, χ₂, hc, travR_spec hP hH F hFG.1 v₁ χ₁ ls (le_of_lt hs₁) (fun _ => hs₁) h₁
          (le_trans (dsize_le_left hc) hn), h₂, le_trans (dsize_le_right hc) hn⟩
      rintro ls' hls r₁ σ ⟨σ₁, σ₂, hcσ, hr₁, hv₂, hn₂⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ r₁ _ σ ?_
      rw [tensorR_body₂]
      refine wpTS_bind_frame _ _ ls' (fun ls'' r => vP (G.resR R) ls'' δ r)
        (fun ls'' => vP (F.resR R) ls'' δ r₁)
        _ (fun ls'' hls' ρ hρ => vP_same hls' hρ) ?_ σ
        ⟨σ₂, σ₁, ResU.CompS.comm hcσ, travR_spec hP hH G hFG.2 v₂ σ₂ ls' (le_of_lt hs₂)
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
        refine travR_app _ h _ ls _ χ ?_
        rw [tR_sum]
        refine wpTS_sum₁ ls v _ _ _ χ ?_
        rw [sumR_branch F h v Expr.inj₁ (fun _ _ _ => rfl)]
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (travR_spec hP hH F hFG.1 v χ ls (le_of_lt hsz) (fun _ => hsz) hv hn)
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        exact wpTS_val ls' (Val.inj₁ r) _ ρ (Or.inl ⟨r, pure_sep_iff.mpr ⟨rfl, hr⟩⟩)
      · obtain ⟨hw, hv⟩ := pure_sep_iff.mp hs
        subst hw
        have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₂ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine travR_app _ h _ ls _ χ ?_
        rw [tR_sum]
        refine wpTS_sum₂ ls v _ _ _ χ ?_
        rw [sumR_branch G h v Expr.inj₂ (fun _ _ _ => rfl)]
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (travR_spec hP hH G hFG.2 v χ ls (le_of_lt hsz) (fun _ => hsz) hv hn)
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        exact wpTS_val ls' (Val.inj₂ r) _ ρ (Or.inr ⟨r, pure_sep_iff.mpr ⟨rfl, hr⟩⟩)

/-! ### Induction on the resource size, then on the value -/

/-- **The recursive call**, at every resource bound `n` and value bound `K`. -/
theorem hRSpec_all {F : FShape} (hF : F.WF) (hG : F.Guarded) {R : VTy} {δ : LSub} {g : Val}
    (hg : ∀ ls, vC true (algRTy F R) ls δ g PMap.empty) :
    ∀ n K, HRSpec (.mu F.ty) R δ n K (hR F g) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    have hP : ∀ w ρ ls, vP (.mu F.ty) ls δ w ρ → dsize ρ < n →
        wpTS ls (.app (.val (hR F g)) (.val w)) (fun ls' v => vP R ls' δ v) ρ :=
      fun w ρ ls hv hlt => ihn (dsize ρ) hlt (sizeOf w.1 + 1) w ρ ls (Nat.lt_succ_self _) hv le_rfl
    intro K
    induction K with
    | zero => intro w χ ls hlt; exact absurd hlt (Nat.not_lt_zero _)
    | succ K ihK =>
        intro w χ ls hlt hv hn
        refine hR_app F g w ls _ χ ?_
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (travR_spec hP ihK F hF w χ ls (Nat.lt_succ_iff.mp hlt)
            (fun e => by subst e; exact hG.elim) (vC_unfold hv).2.2 hn)
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        rw [algR_subst]
        obtain ⟨-, hthunk⟩ := hg ls'
        exact hthunk ls' (Ext.refl _ _) r ρ ρ hr (ResU.CompS.comm (ResU.comp_empty_right ρ))

/-! ### The rule -/

/-- **The owned fold is sound.**  `foldOwn : !U(A′_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)` at every `T`
of the class `FShape` and every `R`. -/
theorem foldReuse_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (F : FShape) (hF : F.WF) (hG : F.Guarded)
    (R : VTy) (hΓ : Ctx.Dead Γ) :
    SemV Δ Γ (.val (foldReuseV F)) (.lolli (algRTy F R) (foldOTy F R)) := by
  intro δ γ ls ρ _ hg₀
  have hρ : ρ = PMap.empty := gSepC_dead hΓ (gDenC_iff.mp hg₀).2
  subst hρ
  rw [substAll_closed (foldReuseV_closed F)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ g ρ₁ τ₀ hv₁ hcomp
  have hρ₁ : ρ₁ = PMap.empty := hv₁.1
  subst hρ₁
  have hg : ∀ ls, vC true (algRTy F R) ls δ g PMap.empty := fun ls' =>
    vC_local true _ (ext_empty ls₁ ls') hv₁
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_lolli _ _ g _ _ ?_
  rw [foldReuseV_subst]
  refine wpTS_val _ _ _ _ ⟨rfl, ?_⟩
  intro ls₂ _ v ρ₂ τ hv hc
  rw [eq_of_compS_empty_left hc]
  exact hRSpec_all hF hG hg (dsize ρ₂) (sizeOf v.1 + 1) v ρ₂ ls₂ (Nat.lt_succ_self _) hv le_rfl

end BoCa.Fig16.LogRel.CBPVMu

end
