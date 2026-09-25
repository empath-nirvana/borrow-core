import Core.Family
import Core.Steps
import Core.Weaken

/-!
# Core — borrowing a block through its leaf family  `[spec §5]`

`experiments/LeafPlaces`' `withborS` at `Blocks.lean`'s shapes.  A block of shape `σ` has the
handle `refTy σ`, the family of its leaf references; `withborS σ` borrows every leaf and hands
the callback the family of leaf borrows at **one** lifetime:

    withborS σ : refTy σ ⊸ (∀'c ⊏ ⊓Δ. famTy M 'c σ ⊸ ['c] T) ⊸ refTy σ ⊗ T      (M = Mut, Imm)

    withborS (leaf A)     ≜ withbor
    withborS (node s₁ s₂) ≜ λp. λg. let (x, y) = p;
                  let (x′, r) = withborS s₁ x (Λ. λmx.
                                  let (y′, t) = withborS s₂ y (Λ. λmy. g () (⇓s₁ mx, my));
                                  (y′, t));
                  let (y′, t) = r; ((x′, y′), t)

`⇓σ e` (`shortenE`) rebuilds a family leaf by leaf; its typing applies `⊑Mut`/`⊑Imm` at every
leaf, and at run time it is the identity (`shortenE_run`).  The rule is a derived rule of
`CDerives` (`withborS_wf`, by induction on the shape), so `fundamentalC` covers it.

Leaves and the result `T` are `plainV`: built from `1`, `0`, `⊗`, `⊕`, `Ref`, `!`, `X` and `μ`,
with no lifetime and no `U C`.  A leaf may be a list.  The result is boxed at the outer
lifetime at every node, and `VOutlives` has no rule at `U C` or `Unk`.

**Borrowing returns the handle it was given** (`withborS_ret`, on every run, through the step
inversions of `Steps.lean`), so after the borrow the handle is again the block's, packed
(`withborS_packed`, `wpTS_allocBorrow`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar LSubst)
open BoCa.Programs (lam app2 alloc' free')

/-! ### Plain types -/

/-- Types with no lifetime and no `U C`: `1`, `0`, `⊗`, `⊕`, `Ref`, `!`, `X`, `μ`. -/
def plainV : VTy → Bool
  | .unit => true
  | .zero => true
  | .tensor A B => plainV A && plainV B
  | .sum A B => plainV A && plainV B
  | .ref A => plainV A
  | .bang A => plainV A
  | .tvar _ => true
  | .mu A => plainV A
  | _ => false

theorem plain_noFree {x : LifeVar} : ∀ {A : VTy}, plainV A = true → ¬ VFree x A
  | .unit, _ => id
  | .zero, _ => id
  | .tensor _ _, h => by
      simp only [plainV, Bool.and_eq_true] at h
      simp only [VFree, not_or]; exact ⟨plain_noFree h.1, plain_noFree h.2⟩
  | .sum _ _, h => by
      simp only [plainV, Bool.and_eq_true] at h
      simp only [VFree, not_or]; exact ⟨plain_noFree h.1, plain_noFree h.2⟩
  | .ref _, h => by simp only [plainV] at h; simp only [VFree]; exact plain_noFree h
  | .bang _, h => by simp only [plainV] at h; simp only [VFree]; exact plain_noFree h
  | .tvar _, _ => id
  | .mu _, h => by simp only [plainV] at h; simp only [VFree]; exact plain_noFree h

theorem plain_lsub {τ : LSubst} : ∀ {A : VTy}, plainV A = true → A.applyLSub τ = A
  | .unit, _ => rfl
  | .zero, _ => rfl
  | .tensor _ _, h => by
      simp only [plainV, Bool.and_eq_true] at h
      simp [VTy.applyLSub, plain_lsub h.1, plain_lsub h.2]
  | .sum _ _, h => by
      simp only [plainV, Bool.and_eq_true] at h
      simp [VTy.applyLSub, plain_lsub h.1, plain_lsub h.2]
  | .ref _, h => by simp only [plainV] at h; simp [VTy.applyLSub, plain_lsub h]
  | .bang _, h => by simp only [plainV] at h; simp [VTy.applyLSub, plain_lsub h]
  | .tvar _, _ => rfl
  | .mu _, h => by simp only [plainV] at h; simp [VTy.applyLSub, plain_lsub h]

theorem plain_outlives {Δ : LifeCtx} {a : Lifetime.Life} :
    ∀ {A : VTy}, plainV A = true → VOutlives Δ a A
  | .unit, _ => .unit
  | .zero, _ => .zero
  | .tensor _ _, h => by
      simp only [plainV, Bool.and_eq_true] at h
      exact .tensor (plain_outlives h.1) (plain_outlives h.2)
  | .sum _ _, h => by
      simp only [plainV, Bool.and_eq_true] at h
      exact .sum (plain_outlives h.1) (plain_outlives h.2)
  | .ref _, h => by simp only [plainV] at h; exact .ref (plain_outlives h)
  | .bang _, _ => .bang
  | .tvar _, _ => .tvar
  | .mu _, h => by simp only [plainV] at h; exact .mu (plain_outlives h)

/-! ### Shapes: plain leaves and the family of leaf borrows -/

namespace Shape

/-- Every leaf type is plain. -/
def plain : Shape → Bool
  | .leaf A => plainV A
  | .node s₁ s₂ => plain s₁ && plain s₂

/-- The family of leaf borrows `M @a A₁ ⊗ …` at one lifetime `@a`.  `[spec §5]` -/
def famTy (M : Lifetime.Life → VTy → VTy) (a : Lifetime.Life) : Shape → VTy
  | .leaf A => M a A
  | .node s₁ s₂ => .tensor (famTy M a s₁) (famTy M a s₂)

theorem refTy_plain : ∀ {σ : Shape}, σ.plain = true → plainV σ.refTy = true
  | .leaf _, h => by simpa [plain, refTy, plainV] using h
  | .node _ _, h => by
      simp only [plain, Bool.and_eq_true] at h
      simp [refTy, plainV, refTy_plain h.1, refTy_plain h.2]

theorem valTy_plain : ∀ {σ : Shape}, σ.plain = true → plainV σ.valTy = true
  | .leaf _, h => by simpa [plain, valTy] using h
  | .node _ _, h => by
      simp only [plain, Bool.and_eq_true] at h
      simp [valTy, plainV, valTy_plain h.1, valTy_plain h.2]

end Shape

/-! ### The leaf formers `Mut` and `Imm` -/

/-- What the block construction needs of the borrow former `M`: `Borrows` (its `withbor`
typing and its `⊑` rule), that `M` commutes with lifetime substitution, and that the
`withbor` side condition holds at plain payloads. -/
structure Former (M : Lifetime.Life → VTy → VTy) (side : LifeCtx → VTy → Prop) : Prop where
  bw : Borrows M side
  lsubM : ∀ τ a S, (M a S).applyLSub τ = M (a.applySub τ) (S.applyLSub τ)
  side_plain : ∀ Δ S, plainV S = true → side Δ S

theorem formerMut : Former mutM (fun Δ S => ∃ b, Δ.Defines b ∧ VOutlives Δ b S) :=
  ⟨borrowsMut, fun _ _ _ => rfl, fun _ _ h => ⟨.top, LifeCtx.defines_of_wf rfl, plain_outlives h⟩⟩

theorem formerImm : Former immM (fun Δ S => VScoped Δ S) :=
  ⟨borrowsImm, fun _ _ _ => rfl, fun _ _ h y hy => absurd hy (plain_noFree h)⟩

section
variable {M : Lifetime.Life → VTy → VTy} {side : LifeCtx → VTy → Prop}

theorem famTy_free (F : Former M side) {a : Lifetime.Life} {z : LifeVar} :
    ∀ {σ : Shape}, σ.plain = true → VFree z (σ.famTy M a) → a.mentions z = true
  | .leaf _, h, hv => by
      rcases (F.bw.free _ _ _).mp hv with h' | h'
      · exact h'
      · exact absurd h' (plain_noFree h)
  | .node _ _, h, hv => by
      simp only [Shape.plain, Bool.and_eq_true] at h
      rcases hv with hv | hv
      · exact famTy_free F h.1 hv
      · exact famTy_free F h.2 hv

theorem famTy_lsub (F : Former M side) {a : Lifetime.Life} {τ : LSubst} :
    ∀ {σ : Shape}, σ.plain = true → (σ.famTy M a).applyLSub τ = σ.famTy M (a.applySub τ)
  | .leaf _, h => by simp [Shape.famTy, F.lsubM, plain_lsub (τ := τ) (by simpa [Shape.plain] using h)]
  | .node _ _, h => by
      simp only [Shape.plain, Bool.and_eq_true] at h
      simp [Shape.famTy, VTy.applyLSub, famTy_lsub F h.1, famTy_lsub F h.2]

/-- `∀'c ⊏ @bnd. famTy M 'c σ ⊸ ['c] T`. -/
def cbT (M : Lifetime.Life → VTy → VTy) (c : LifeVar) (bnd : Lifetime.Life) (σ : Shape)
    (T : VTy) : VTy :=
  .all c bnd (.lolli (σ.famTy M (.var c)) (.box (.var c) T))

/-- `refTy σ ⊸ cbT ⊸ refTy σ ⊗ T`. -/
def wTy (M : Lifetime.Life → VTy → VTy) (c : LifeVar) (bnd : Lifetime.Life) (σ : Shape)
    (T : VTy) : VTy :=
  .lolli σ.refTy (.lolli (cbT M c bnd σ T) (.tensor σ.refTy T))

theorem cbT_inst (F : Former M side) {c : LifeVar} {a : Lifetime.Life} {σ : Shape} {T : VTy}
    (hσ : σ.plain = true) (hT : plainV T = true) :
    VTy.instLife c a (.lolli (σ.famTy M (.var c)) (.box (.var c) T))
      = .lolli (σ.famTy M a) (.box a T) := by
  simp [VTy.instLife, VTy.applyLSub, CTy.applyLSub, famTy_lsub F hσ, plain_lsub hT,
    Lifetime.Life.applySub, Lifetime.assocFind]

theorem cbT_free (F : Former M side) {c z : LifeVar} {bnd : Lifetime.Life} {σ : Shape} {T : VTy}
    (hσ : σ.plain = true) (hT : plainV T = true) (hb : bnd.mentions z = false) (hz : c ≠ z) :
    ¬ VFree z (cbT M c bnd σ T) := by
  intro h
  simp only [cbT, VTy.all, VTy.lolli, VFree, CFree] at h
  rcases h with h | ⟨-, (h | h | h)⟩
  · rw [hb] at h; cases h
  · have := famTy_free F hσ h
    simp [Lifetime.Life.mentions] at this; exact hz this.symm
  · simp [Lifetime.Life.mentions] at h; exact hz h.symm
  · exact plain_noFree hT h

end

/-! ### Closed terms -/

/-! ## Closed terms -/

/-- Every free de Bruijn index of the term is below `n`. -/
def clAt : Nat → Expr → Bool
  | n, .var i => decide (i < n)
  | _, .unit => true
  | n, .pair a b => clAt n a && clAt n b
  | n, .inj₁ a => clAt n a
  | n, .inj₂ a => clAt n a
  | n, .lam b => clAt (n + 1) b
  | _, .loc _ => true
  | _, .prim _ => true
  | n, .seq a b => clAt n a && clAt n b
  | n, .letpair a b => clAt n a && clAt (n + 2) b
  | n, .case a b c => clAt n a && clAt (n + 1) b && clAt (n + 1) c
  | n, .app a b => clAt n a && clAt n b

theorem subst_clAt : ∀ (e : Expr) {n j : Nat} (s : Val), clAt n e = true → n ≤ j →
    e.subst j s = e
  | .var i, n, j, s, h, hj => by
      simp only [clAt, decide_eq_true_eq] at h
      have e₁ : ¬ i = j := by omega
      have e₂ : ¬ i > j := by omega
      simp [Expr.subst, e₁, e₂]
  | .unit, _, _, _, _, _ => rfl
  | .pair a b, _, _, s, h, hj => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.subst, subst_clAt a s h.1 hj, subst_clAt b s h.2 hj]
  | .inj₁ a, _, _, s, h, hj => by simp only [clAt] at h; simp [Expr.subst, subst_clAt a s h hj]
  | .inj₂ a, _, _, s, h, hj => by simp only [clAt] at h; simp [Expr.subst, subst_clAt a s h hj]
  | .lam b, n, j, s, h, hj => by
      simp only [clAt] at h; simp [Expr.subst, subst_clAt b (n := n + 1) (j := j + 1) _ h (by omega)]
  | .loc _, _, _, _, _, _ => rfl
  | .prim _, _, _, _, _, _ => rfl
  | .seq a b, _, _, s, h, hj => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.subst, subst_clAt a s h.1 hj, subst_clAt b s h.2 hj]
  | .letpair a b, n, j, s, h, hj => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.subst, subst_clAt a s h.1 hj, subst_clAt b (n := n + 2) (j := j + 2) _ h.2 (by omega)]
  | .case a b c, n, j, s, h, hj => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.subst, subst_clAt a s h.1.1 hj,
        subst_clAt b (n := n + 1) (j := j + 1) _ h.1.2 (by omega),
        subst_clAt c (n := n + 1) (j := j + 1) _ h.2 (by omega)]
  | .app a b, _, _, s, h, hj => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.subst, subst_clAt a s h.1 hj, subst_clAt b s h.2 hj]

theorem shift_clAt : ∀ (e : Expr) {n c : Nat} (d : Nat), clAt n e = true → n ≤ c →
    e.shift d c = e
  | .var i, n, c, d, h, hc => by
      simp only [clAt, decide_eq_true_eq] at h
      have e₁ : i < c := by omega
      simp [Expr.shift, e₁]
  | .unit, _, _, _, _, _ => rfl
  | .pair a b, _, _, d, h, hc => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.shift, shift_clAt a d h.1 hc, shift_clAt b d h.2 hc]
  | .inj₁ a, _, _, d, h, hc => by simp only [clAt] at h; simp [Expr.shift, shift_clAt a d h hc]
  | .inj₂ a, _, _, d, h, hc => by simp only [clAt] at h; simp [Expr.shift, shift_clAt a d h hc]
  | .lam b, n, c, d, h, hc => by
      simp only [clAt] at h; simp [Expr.shift, shift_clAt b (n := n + 1) (c := c + 1) d h (by omega)]
  | .loc _, _, _, _, _, _ => rfl
  | .prim _, _, _, _, _, _ => rfl
  | .seq a b, _, _, d, h, hc => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.shift, shift_clAt a d h.1 hc, shift_clAt b d h.2 hc]
  | .letpair a b, n, c, d, h, hc => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.shift, shift_clAt a d h.1 hc, shift_clAt b (n := n + 2) (c := c + 2) d h.2 (by omega)]
  | .case a b c, n, c', d, h, hc => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.shift, shift_clAt a d h.1.1 hc,
        shift_clAt b (n := n + 1) (c := c' + 1) d h.1.2 (by omega),
        shift_clAt c (n := n + 1) (c := c' + 1) d h.2 (by omega)]
  | .app a b, _, _, d, h, hc => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [Expr.shift, shift_clAt a d h.1 hc, shift_clAt b d h.2 hc]

theorem occ_clAt : ∀ (e : Expr) {n i : Nat}, clAt n e = true → n ≤ i → occ i e = false
  | .var j, n, i, h, hi => by
      simp only [clAt, decide_eq_true_eq] at h
      simp only [occ, beq_eq_false_iff_ne]; omega
  | .unit, _, _, _, _ => rfl
  | .pair a b, _, _, h, hi => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [occ, occ_clAt a h.1 hi, occ_clAt b h.2 hi]
  | .inj₁ a, _, _, h, hi => by simp only [clAt] at h; simp [occ, occ_clAt a h hi]
  | .inj₂ a, _, _, h, hi => by simp only [clAt] at h; simp [occ, occ_clAt a h hi]
  | .lam b, n, i, h, hi => by
      simp only [clAt] at h; simp [occ, occ_clAt b (n := n + 1) (i := i + 1) h (by omega)]
  | .loc _, _, _, _, _ => rfl
  | .prim _, _, _, _, _ => rfl
  | .seq a b, _, _, h, hi => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [occ, occ_clAt a h.1 hi, occ_clAt b h.2 hi]
  | .letpair a b, n, i, h, hi => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [occ, occ_clAt a h.1 hi, occ_clAt b (n := n + 2) (i := i + 2) h.2 (by omega)]
  | .case a b c, n, i, h, hi => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [occ, occ_clAt a h.1.1 hi, occ_clAt b (n := n + 1) (i := i + 1) h.1.2 (by omega),
        occ_clAt c (n := n + 1) (i := i + 1) h.2 (by omega)]
  | .app a b, _, _, h, hi => by
      simp only [clAt, Bool.and_eq_true] at h
      simp [occ, occ_clAt a h.1 hi, occ_clAt b h.2 hi]

theorem clAt_mono : ∀ (e : Expr) {n m : Nat}, clAt n e = true → n ≤ m → clAt m e = true
  | .var j, n, m, h, hm => by
      simp only [clAt, decide_eq_true_eq] at h ⊢; omega
  | .unit, _, _, _, _ => rfl
  | .pair a b, _, _, h, hm => by
      simp only [clAt, Bool.and_eq_true] at h ⊢; exact ⟨clAt_mono a h.1 hm, clAt_mono b h.2 hm⟩
  | .inj₁ a, _, _, h, hm => by simp only [clAt] at h ⊢; exact clAt_mono a h hm
  | .inj₂ a, _, _, h, hm => by simp only [clAt] at h ⊢; exact clAt_mono a h hm
  | .lam b, n, m, h, hm => by
      simp only [clAt] at h ⊢; exact clAt_mono b (n := n + 1) (m := m + 1) h (by omega)
  | .loc _, _, _, _, _ => rfl
  | .prim _, _, _, _, _ => rfl
  | .seq a b, _, _, h, hm => by
      simp only [clAt, Bool.and_eq_true] at h ⊢; exact ⟨clAt_mono a h.1 hm, clAt_mono b h.2 hm⟩
  | .letpair a b, n, m, h, hm => by
      simp only [clAt, Bool.and_eq_true] at h ⊢
      exact ⟨clAt_mono a h.1 hm, clAt_mono b (n := n + 2) (m := m + 2) h.2 (by omega)⟩
  | .case a b c, n, m, h, hm => by
      simp only [clAt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨clAt_mono a h.1.1 hm, clAt_mono b (n := n + 1) (m := m + 1) h.1.2 (by omega)⟩,
        clAt_mono c (n := n + 1) (m := m + 1) h.2 (by omega)⟩
  | .app a b, _, _, h, hm => by
      simp only [clAt, Bool.and_eq_true] at h ⊢; exact ⟨clAt_mono a h.1 hm, clAt_mono b h.2 hm⟩

/-- A closed value is fixed by shifting. -/
theorem Val.shift_cl {v : Val} (h : clAt 0 v.1 = true) (d c : Nat) : v.shift d c = v :=
  Val.ext (shift_clAt v.1 d h (Nat.zero_le c))

/-! ### The operations -/

/-- `⇓σ e`: the family `e`, rebuilt leaf by leaf. -/
def shortenE : Shape → Expr → Expr
  | .leaf _, e => e
  | .node s₁ s₂, e => .letpair e (.pair (shortenE s₁ (.var 1)) (shortenE s₂ (.var 0)))

/-- Borrow a struct: every leaf, the family handed to the callback at one lifetime.  `[spec §5]` -/
def withborS : Shape → Expr
  | .leaf _ => withbor
  | .node s₁ s₂ =>
      lam2 (.letpair (.var 1)
        (.letpair (app2 (withborS s₁) (.var 1)
            (lam (lam (.letpair (app2 (withborS s₂) (.var 2)
                (lam (lam (app2 (.var 6) unit' (.pair (shortenE s₁ (.var 2)) (.var 0))))))
              (.pair (.var 1) (.var 0))))))
          (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0)))))

/-- The inner callback of `withborS (node s₁ s₂)`: `Λ. λmy. g () (⇓s₁ mx, my)`, `mx` at 2 and
`g` at 6. -/
def innerS (s₁ : Shape) : Expr := lam (lam (app2 (.var 6) unit' (.pair (shortenE s₁ (.var 2)) (.var 0))))

/-- The outer callback: `Λ. λmx. let (y′, t) = withborS s₂ y innerS; (y′, t)`, `y` at 2. -/
def outerS (s₁ s₂ : Shape) : Expr :=
  lam (lam (.letpair (app2 (withborS s₂) (.var 2) (innerS s₁)) (.pair (.var 1) (.var 0))))

theorem withborS_node (s₁ s₂ : Shape) :
    withborS (.node s₁ s₂) =
      lam2 (.letpair (.var 1)
        (.letpair (app2 (withborS s₁) (.var 1) (outerS s₁ s₂))
          (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0))))) := rfl

/-! ## Closedness -/

theorem clAt_shortenE : ∀ (σ : Shape) {n : Nat} {e : Expr}, clAt n e = true →
    clAt n (shortenE σ e) = true
  | .leaf _, _, _, h => h
  | .node s₁ s₂, n, e, h => by
      simp only [shortenE, clAt, Bool.and_eq_true]
      exact ⟨h, clAt_shortenE s₁ (by simp [clAt]), clAt_shortenE s₂ (by simp [clAt])⟩

theorem clAt_allocS : ∀ σ : Shape, clAt 0 (allocS σ) = true
  | .leaf _ => rfl
  | .node s₁ s₂ => by
      simp only [allocS, lam, Val.lam, clAt, Bool.and_eq_true]
      exact ⟨rfl, ⟨clAt_mono _ (clAt_allocS s₁) (by omega), rfl⟩,
        clAt_mono _ (clAt_allocS s₂) (by omega), rfl⟩

theorem clAt_freeS : ∀ σ : Shape, clAt 0 (freeS σ) = true
  | .leaf _ => rfl
  | .node s₁ s₂ => by
      simp only [freeS, lam, Val.lam, clAt, Bool.and_eq_true]
      exact ⟨rfl, ⟨clAt_mono _ (clAt_freeS s₁) (by omega), rfl⟩,
        clAt_mono _ (clAt_freeS s₂) (by omega), rfl⟩

theorem clAt_withborS : ∀ σ : Shape, clAt 0 (withborS σ) = true
  | .leaf _ => rfl
  | .node s₁ s₂ => by
      have h₁ : ∀ n, clAt n (withborS s₁) = true := fun n => clAt_mono _ (clAt_withborS s₁) (Nat.zero_le n)
      have h₂ : ∀ n, clAt n (withborS s₂) = true := fun n => clAt_mono _ (clAt_withborS s₂) (Nat.zero_le n)
      have h₃ : clAt 8 (shortenE s₁ (.var 2)) = true := clAt_shortenE s₁ (by simp [clAt])
      simp [withborS, lam2, lam, app2, Val.lam, unit', Val.unit, clAt, h₁, h₂, h₃]

/-- `allocS σ`, `freeS σ` and `withborS σ` as values. -/
def allocV (σ : Shape) : Val :=
  match σ with
  | .leaf _ => .prim .alloc
  | .node s₁ s₂ => .lam (.letpair (.var 0) (.pair (.app (allocS s₁) (.var 1)) (.app (allocS s₂) (.var 0))))

theorem allocV_val (σ : Shape) : (allocV σ).1 = allocS σ := by cases σ <;> rfl

def freeV (σ : Shape) : Val :=
  match σ with
  | .leaf _ => .prim .free
  | .node s₁ s₂ => .lam (.letpair (.var 0) (.pair (.app (freeS s₁) (.var 1)) (.app (freeS s₂) (.var 0))))

theorem freeV_val (σ : Shape) : (freeV σ).1 = freeS σ := by cases σ <;> rfl

theorem isVal_withborS : ∀ σ : Shape, IsVal (withborS σ)
  | .leaf _ => .lam
  | .node _ _ => .lam

def withborV (σ : Shape) : Val := ⟨withborS σ, isVal_withborS σ⟩

theorem clAt_addr : ∀ (σ : Shape) (b : Loc), clAt 0 (σ.addr b).1 = true
  | .leaf _, _ => rfl
  | .node s₁ s₂, b => by
      simp only [Shape.addr, Val.pair, clAt, Bool.and_eq_true]
      exact ⟨clAt_addr s₁ b, clAt_addr s₂ _⟩


/-! ### Typing -/

theorem assocFind_none_of_gt {β : Type} (x : LifeVar) :
    ∀ l : List (LifeVar × β), (∀ p ∈ l, p.1 < x) → Lifetime.assocFind x l = none
  | [], _ => rfl
  | (k, v) :: t, h => by
      have hk : k ≠ x := Nat.ne_of_lt (h (k, v) (List.mem_cons_self ..))
      simp only [Lifetime.assocFind, hk, if_false]
      exact assocFind_none_of_gt x t fun p hp => h p (List.mem_cons_of_mem _ hp)

theorem exists_fresh_var (Δ : LifeCtx) (c : LifeVar) : ∃ x, Δ.find? x = none ∧ x ≠ c := by
  refine ⟨c + 1 + (Δ.entries.map Prod.fst).sum, assocFind_none_of_gt _ _ fun p hp => ?_, ?_⟩
  · have h₁ : p.1 ≤ (Δ.entries.map Prod.fst).sum := List.le_sum_of_mem (List.mem_map_of_mem hp)
    exact Nat.lt_of_le_of_lt h₁ (Nat.lt_add_of_pos_left (Nat.succ_pos c))
  · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self c) (Nat.le_add_right _ _))

section
variable {M : Lifetime.Life → VTy → VTy} {side : LifeCtx → VTy → Prop}

/-- `⇓σ`: a family moved to a shorter lifetime, leaf by leaf.  `[spec §5]` -/
theorem shortenE_wf (F : Former M side) : ∀ {σ : Shape}, σ.plain = true →
    ∀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life},
    CDerives Δ Γ e (.val (σ.famTy M b)) → Δ.EntailsLe a b →
    CDerives Δ Γ (shortenE σ e) (.val (σ.famTy M a))
  | .leaf _, _, _, _, _, _, _, h, hle => F.bw.sub h hle
  | .node s₁ s₂, hσ, _, Γ, _, _, _, h, hle => by
      simp only [Shape.plain, Bool.and_eq_true] at hσ
      refine .letpairV (split_kill' Γ).toP h ?_
      exact .tensorI (.right (.left (deadSplit (kill_dead Γ))))
        (shortenE_wf F hσ.1 (.var (.there (.here (kill_dead Γ)))) hle)
        (shortenE_wf F hσ.2 (.var (.here (.cons (kill_dead Γ)))) hle)

theorem nf_cons {x : LifeVar} {Γ : Ctx VTy} {S : VTy} {l : Bool} (h : l = true → ¬ VFree x S)
    (hΓ : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) :
    ∀ s ∈ (⟨S, l⟩ :: Γ : Ctx VTy), s.live = true → ¬ VFree x s.ty := by
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs
  · exact h hl
  · exact hΓ s hs hl

/-- **The derived rule.**  `withborS σ : refTy σ ⊸ (∀'c ⊏ ⊓Δ. famTy M 'c σ ⊸ ['c] T) ⊸
refTy σ ⊗ T`, at `M = Mut` (`formerMut`) and `M = Imm` (`formerImm`).  `[spec §5]` -/
theorem withborS_wf (F : Former M side) : ∀ {σ : Shape}, σ.plain = true →
    ∀ {Δ : LifeCtx} {Γ : Ctx VTy} (c : LifeVar) {T : VTy}, plainV T = true → Δ.Ok →
    Δ.find? c = none → Ctx.Dead Γ → CDerives Δ Γ (withborS σ) (.val (wTy M c Δ.meetOfDom σ T))
  | .leaf S, hσ, Δ, _, c, T, hT, _, hc, hΓ =>
      F.bw.ax c hΓ hc (F.side_plain Δ S hσ) (plain_noFree hσ) (plain_noFree hT)
  | .node s₁ s₂, hσ, Δ, Γ, c, T, hT, hΔ, hc, hΓ => by
      have hσ' := hσ
      simp only [Shape.plain, Bool.and_eq_true] at hσ'
      obtain ⟨hp₁, hp₂⟩ := hσ'
      obtain ⟨x, hx, hxc⟩ := exists_fresh_var Δ c
      obtain ⟨y, hy, hyc⟩ := exists_fresh_var (FD₁ Δ x) c
      have hxy : x ≠ y := by
        intro e; subst e; simp [FD₁, LifeCtx.find?_extend] at hy
      have hyΔ : Δ.find? y = none := by
        have := hy; simp [FD₁, LifeCtx.find?_extend, hxy] at this; exact this
      have hΔ₁ : (FD₁ Δ x).Ok := hΔ.extend hx (Lifetime.meetOfDomL_wf _)
      have hR₂ := Shape.refTy_plain hp₂
      have hT' : plainV (.tensor s₂.refTy T) = true := by simp [plainV, hR₂, hT]
      have hbx : Δ.meetOfDom.mentions x = false :=
        Lifetime.Life.mentions_false_of_wf hx (Lifetime.meetOfDomL_wf _)
      have hby : Δ.meetOfDom.mentions y = false :=
        Lifetime.Life.mentions_false_of_wf hyΔ (Lifetime.meetOfDomL_wf _)
      -- the inner callback, at `Δ, 'x`
      have hinner : CDerives (FD₁ Δ x)
          (⟨s₁.famTy M (.var x), true⟩ :: ⟨.unit, false⟩ :: ⟨s₂.refTy, false⟩ ::
            ⟨s₁.refTy, false⟩ :: ⟨cbT M c Δ.meetOfDom (.node s₁ s₂) T, true⟩ ::
            ⟨(Shape.node s₁ s₂).refTy, false⟩ :: Γ)
          (innerS s₁) (.val (cbT M y (FD₁ Δ x).meetOfDom s₂ T)) := by
        refine .thunkV rfl (.allI (S := .unit)
          (Lifetime.Life.mentions_false_of_wf hy (Lifetime.meetOfDomL_wf _))
          (fun _ _ h => hΔ₁.bound_mentions_false hy h) ?_ (.ret (.lamV ?_)))
        · refine nf_cons (fun _ h => ?_) (nf_cons (by simp) (nf_cons (by simp) (nf_cons (by simp)
            (nf_cons (fun _ => cbT_free F hσ hT hby (Ne.symm hyc))
              (nf_cons (by simp) (dead_noLive hΓ (P := fun s => ¬ VFree y s.ty))))))) 
          have := famTy_free F hp₁ h
          simp [Lifetime.Life.mentions] at this; exact hxy this.symm
        have hg := CDerives.allEV (Δ := FD₂ Δ x y) (a := .var y)
          (Γ := ⟨s₂.famTy M (.var y), false⟩ :: ⟨.unit, false⟩ :: ⟨s₁.famTy M (.var x), false⟩ ::
            ⟨.unit, false⟩ :: ⟨s₂.refTy, false⟩ :: ⟨s₁.refTy, false⟩ ::
            ⟨cbT M c Δ.meetOfDom (.node s₁ s₂) T, true⟩ :: ⟨(Shape.node s₁ s₂).refTy, false⟩ :: Γ)
          (.var (.there (.there (.there (.there (.there (.there (.here (.cons hΓ)))))))))
          (entailsLt_inner Δ x y)
        rw [cbT_inst F hσ hT] at hg
        refine .lolliE (.left (.dead (.left (.dead (.dead (.dead (.right (.dead (deadSplit hΓ)))))))))
          ?_ hg
        refine .tensorI (.right (.dead (.left (.dead (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))))
          ?_ (.var (.here (by cdead)))
        exact shortenE_wf F hp₁ (.var (.there (.there (.here (by cdead)))))
          (entailsLe_inner Δ x y)
      -- the outer callback, at `Δ`
      have houter : CDerives Δ
          (⟨s₂.refTy, true⟩ :: ⟨s₁.refTy, false⟩ :: ⟨cbT M c Δ.meetOfDom (.node s₁ s₂) T, true⟩ ::
            ⟨(Shape.node s₁ s₂).refTy, false⟩ :: Γ)
          (outerS s₁ s₂) (.val (cbT M x Δ.meetOfDom s₁ (.tensor s₂.refTy T))) := by
        refine .thunkV rfl (.allI (S := .unit) hbx (fun _ _ h => hΔ.bound_mentions_false hx h) ?_
          (.ret (.lamV ?_)))
        · exact nf_cons (fun _ => plain_noFree hR₂) (nf_cons (by simp)
            (nf_cons (fun _ => cbT_free F hσ hT hbx (Ne.symm hxc)) (nf_cons (by simp)
              (dead_noLive hΓ (P := fun s => ¬ VFree x s.ty)))))
        refine .letpairV (A := s₂.refTy) (B := T)
          (.left (.dead (.left (.dead (.left (.dead (deadSplit hΓ))))))) ?_ ?_
        · refine .lolliE (.left (.dead (.right (.dead (.left (.dead (deadSplit hΓ))))))) hinner ?_
          exact .lolliE (.dead (.dead (.left (.dead (.dead (.dead (deadSplit hΓ)))))))
            (.var (.there (.there (.here (by cdead))))) (withborS_wf F hp₂ y hT hΔ₁ hy (by cdead))
        · exact .boxI (.tensorI (.right (.left (deadSplit (by cdead))))
              (.var (.there (.here (by cdead)))) (.var (.here (by cdead))))
            (outlives_two (LifeCtx.defines_of_wf (wf_var_self _ _ _)) (plain_outlives hT)
              (plain_outlives hR₂) (by cdead))
      -- the family rule
      refine .lamV (.lamV ?_)
      refine .letpairV (.right (.left (deadSplit hΓ))) (.var (.there (.here hΓ))) ?_
      refine .letpairV (A := s₁.refTy) (B := .tensor s₂.refTy T)
        (.left (.left (.left (.dead (deadSplit hΓ))))) ?_ ?_
      · refine .lolliE (.left (.right (.left (.dead (deadSplit hΓ))))) houter ?_
        exact .lolliE (.dead (.left (.dead (.dead (deadSplit hΓ))))) (.var (.there (.here (by cdead))))
          (withborS_wf F hp₁ x hT' hΔ hx (by cdead))
      refine .letpairV (A := s₂.refTy) (B := T) (.left (.right (deadSplit (by cdead))))
        (.var (.here (by cdead))) ?_
      exact .tensorI (.right (.left (.dead (.left (deadSplit (by cdead))))))
        (.tensorI (.dead (.right (.dead (.left (deadSplit (by cdead))))))
          (.var (.there (.there (.there (.here (by cdead)))))) (.var (.there (.here (by cdead)))))
        (.var (.here (by cdead)))

/-- `withborS` at `Mut`: every leaf mutably borrowed at one lifetime.  `[spec §5]` -/
theorem withborSM_wf {σ : Shape} (hσ : σ.plain = true) {Δ : LifeCtx} {Γ : Ctx VTy} (c : LifeVar)
    {T : VTy} (hT : plainV T = true) (hΔ : Δ.Ok) (hc : Δ.find? c = none) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (withborS σ) (.val (wTy mutM c Δ.meetOfDom σ T)) :=
  withborS_wf formerMut hσ c hT hΔ hc hΓ

/-- `withborS` at `Imm`: every leaf immutably borrowed at one lifetime.  `[spec §5]` -/
theorem withborSI_wf {σ : Shape} (hσ : σ.plain = true) {Δ : LifeCtx} {Γ : Ctx VTy} (c : LifeVar)
    {T : VTy} (hT : plainV T = true) (hΔ : Δ.Ok) (hc : Δ.find? c = none) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (withborS σ) (.val (wTy immM c Δ.meetOfDom σ T)) :=
  withborS_wf formerImm hσ c hT hΔ hc hΓ
end

end BoCa.Fig16.LogRel.Core

end
