import EffModelRel.Examples

/-!
# EffModelRel — writers commute (`docs/effects-tr` T7.11)

Two handlers of distinct instances into state-passing types, the inner one with a **pure** clause
(it resumes once with an answer and a next state computed from the argument and the state, and
does nothing else: `PureClause`), commute their operations:

    writer₁(writer₂(op x₁ v₁; op x₂ v₂; M)) ≡ writer₁(writer₂(op x₂ v₂; op x₁ v₁; M))

The TR's proof is an equation of denotations. It holds only where the inner handler's fresh
instance differs from the outer one; the denotation is a function of the fresh name, and where the
two coincide and the effects agree the inner handler catches both operations. So the proof goes
through the relation, whose world says the inner name is fresh (`TreeRel.nu_congr`): a `ν` is
related through its body at free names only.
-/

namespace EffRel

variable {S : Sig}

/-- A tree relation reads a `ν`'s body only at names free in the world. -/
theorem TreeRel.nu_congr {R : W → X → X → Prop} {w : W} {k₁ k₂ : Nat → Tree S X} {t' : Tree S X}
    (h : TreeRel R w (.nu k₂) t') (hk : ∀ i, w.sl i = .free → k₁ i = k₂ i) :
    TreeRel R w (.nu k₁) t' := by
  suffices H : ∀ w t t', TreeRel R w t t' → ∀ k₂, t = .nu k₂ → ∀ k₁ : Nat → Tree S X,
      (∀ i, w.sl i = .free → k₁ i = k₂ i) → TreeRel R w (.nu k₁) t' from H _ _ _ h k₂ rfl k₁ hk
  intro w t t' h
  induction h with
  | ret => intro _ h; cases h
  | op => intro _ h; cases h
  | ab => intro _ h; cases h
  | abE => intro _ h; cases h
  | act => intro _ h; cases h
  | nu hk' _ =>
      intro k₂ h k₁ hk; cases h
      exact .nu (fun i i' hi hi' => (hk i hi) ▸ hk' i i' hi hi')
  | nuL hk' _ =>
      intro k₂ h k₁ hk; cases h
      exact .nuL (fun i hi => (hk i hi) ▸ hk' i hi)
  | gL hk' _ =>
      intro k₂ h k₁ hk; cases h
      exact .gL (fun i hi => (hk i hi) ▸ hk' i hi)
  | mL hi' hk' _ =>
      intro k₂ h k₁ hk; cases h
      exact .mL hi' (fun i hi => (hk i hi) ▸ hk' i hi)
  | nuR _ ih =>
      intro k₂ h k₁ hk; exact .nuR (fun i' hi' => ih i' hi' k₂ h k₁ hk)
  | gR _ ih =>
      intro k₂ h k₁ hk; exact .gR (fun i' hi' => ih i' hi' k₂ h k₁ hk)
  | @mR w t k' i hi _ ih =>
      intro k₂ h k₁ hk
      refine .mR hi (fun i' hi' => ih i' hi' k₂ h k₁ (fun a ha => hk a ?_))
      simp only [W.matchR, W.link, upd] at ha
      by_cases hai : a = i
      · rw [if_pos hai] at ha; cases ha
      · rwa [if_neg hai] at ha

/-- A handler whose body's trees are related, at every world above, by a hypothesis about the two
bodies, relates the two handled computations: the clauses are related to themselves. -/
theorem handle_body_rel {e : S.E} {bk : Rw} {A : VTy S} {C : CTy S}
    {hr : Cmp S Ψ (A :: Γ) C}
    {hop : (o : S.O e) → Cmp S Ψ (kty (S.q e o) bk (S.res e o) C :: .g (S.arg e o) :: Γ) C}
    {hab : (a : S.A e) → Cmp S Ψ (.g (S.aarg e a) :: Γ) C} {M N : Cmp S (e :: Ψ) Γ (.F A)}
    {w : W} (hw : w.noPend) {η η' : IEnv Ψ} {ρ ρ' : Env Γ} (hη : IR w η η') (hρ : ER w ρ ρ')
    (hMN : ∀ i i' (hi : w.sl i = .free) (hi' : w.sr i' = .free),
      TreeRel (fun w a a' => VR A w a a') (w.both i i' hi hi')
        (M.den (η.cons i) ρ) (N.den (η'.cons i') ρ')) :
    CRU C w ((Cmp.handle e bk hr hop hab M).den η ρ) ((Cmp.handle e bk hr hop hab N).den η' ρ') := by
  simp only [Cmp.den]
  apply nuA_both C
  intro i i' hi hi'
  have hs := W.sub_both w i i' hi hi'
  apply hnd_rel C (hMN i i' hi hi') (W.both_r _ _ _ _ _)
  · intro w' h1 hp x x' hx
    exact Cmp.fp hr hp (hη.sub (hs.trans h1)) (ER.cons (hρ.mono (hs.trans h1)) hx)
  · intro w' h1 hp o v k k' d d' hk hd
    exact Cmp.fp (hop o) hp (hη.sub (hs.trans h1))
      (ER.cons (ER.cons (hρ.mono (hs.trans h1)) (VR_g.2 rfl)) (mkK_rel hp hk (dtorsT_rel hp hd)))
  · intro w' h1 hp a v
    exact Cmp.fp (hab a) hp (hη.sub (hs.trans h1)) (ER.cons (hρ.mono (hs.trans h1)) (VR_g.2 rfl))

theorem hnd_op_ne (C : CTy S) {i j : Nat} (hne : j ≠ i) (e : S.E) (hr : X → C.den) (hop) (hab)
    {e' : S.E} (o : S.O e') (v) (k : (S.res e' o).den → Tree S X) (d : List Dtor) :
    (Tree.op j e' o v k d).hnd C i e hr hop hab =
      C.opA j e' o v (fun y => (k y).hnd C i e hr hop hab) d := by
  simp only [Tree.hnd, hne, ↓reduceIte]

/-- The inner writer passes an operation of another name, and its pure clause resumes at once
with the next state: the two orders give the same tree. -/
theorem writer_swap {e₁ e₂ : S.E} {A₂ : VTy S} {b₂ : Rw} {B₂ : VTy S} {X : Type}
    {i₁ i₂ : Nat} (hne : i₁ ≠ i₂) (o₁ : S.O e₁) (o₂ : S.O e₂) (v₁ : (S.arg e₁ o₁).den)
    (v₂ : (S.arg e₂ o₂).den) (hr : X → (CTy.arr A₂ b₂ (.F B₂)).den)
    (hop : (o : S.O e₂) → (S.arg e₂ o).den → ((S.res e₂ o).den → (CTy.arr A₂ b₂ (.F B₂)).den) →
      List Dtor → (CTy.arr A₂ b₂ (.F B₂)).den)
    (hab : (a : S.A e₂) → (S.aarg e₂ a).den → (CTy.arr A₂ b₂ (.F B₂)).den)
    {ans : (S.arg e₂ o₂).den → (S.res e₂ o₂).den} {next : (S.arg e₂ o₂).den → A₂.den → A₂.den}
    (hP : ∀ k d, hop o₂ v₂ k d = fun s => k (ans v₂) (next v₂ s))
    (K K' : (S.res e₁ o₁).den → (S.res e₂ o₂).den → Tree S X) (hK : ∀ y₁ y₂, K y₁ y₂ = K' y₁ y₂)
    (s : A₂.den) :
    (Tree.hnd (.arr A₂ b₂ (.F B₂)) i₂ e₂ hr hop hab
        (.op i₁ e₁ o₁ v₁ (fun y₁ => .op i₂ e₂ o₂ v₂ (fun y₂ => K y₁ y₂) []) [])) s =
      (Tree.hnd (.arr A₂ b₂ (.F B₂)) i₂ e₂ hr hop hab
        (.op i₂ e₂ o₂ v₂ (fun y₂ => .op i₁ e₁ o₁ v₁ (fun y₁ => K' y₁ y₂) []) [])) s := by
  rw [hnd_op_ne _ hne, hnd_op_self, hP]
  simp only [CTy.opA]
  rw [hnd_op_ne _ hne]
  simp only [CTy.opA]
  congr 1; funext y₁
  rw [hnd_op_self, hP, hK]

/-- **Writers commute** (`docs/effects-tr` T7.11). The outer handler is any handler; the inner
one is a handler of a fresh instance into a state-passing type whose clause for `o₂` is pure.
The two operations, on the outer and the inner instance, commute. -/
theorem writers_commute {e₁ e₂ : S.E} {A₁ A₂ B₂ B : VTy S} {b₁ b₂ bk₁ bk₂ : Rw} {D : CTy S}
    (hr₁ : Cmp S Ψ (B₂ :: Γ) (.arr A₁ b₁ D))
    (hop₁ : (o : S.O e₁) → Cmp S Ψ (kty (S.q e₁ o) bk₁ (S.res e₁ o) (.arr A₁ b₁ D) ::
      .g (S.arg e₁ o) :: Γ) (.arr A₁ b₁ D))
    (hab₁ : (a : S.A e₁) → Cmp S Ψ (.g (S.aarg e₁ a) :: Γ) (.arr A₁ b₁ D))
    (hr₂ : Cmp S (e₁ :: Ψ) (B :: Γ) (.arr A₂ b₂ (.F B₂)))
    (hop₂ : (o : S.O e₂) → Cmp S (e₁ :: Ψ) (kty (S.q e₂ o) bk₂ (S.res e₂ o) (.arr A₂ b₂ (.F B₂)) ::
      .g (S.arg e₂ o) :: Γ) (.arr A₂ b₂ (.F B₂)))
    (hab₂ : (a : S.A e₂) → Cmp S (e₁ :: Ψ) (.g (S.aarg e₂ a) :: Γ) (.arr A₂ b₂ (.F B₂)))
    (o₁ : S.O e₁) (o₂ : S.O e₂) {ans next} (hP : PureClause o₂ (hop₂ o₂) ans next)
    (v₁ : (S.arg e₁ o₁).den) (v₂ : (S.arg e₂ o₂).den)
    (s₁ : Val S Ψ Γ A₁) (s₂ : Val S (e₁ :: Ψ) Γ A₂)
    (M : Cmp S (e₂ :: e₁ :: Ψ) (.g (S.res e₂ o₂) :: .g (S.res e₁ o₁) :: Γ) (.F B)) :
    CtxEq
      (.app (.handle e₁ bk₁ hr₁ hop₁ hab₁ (.app (.handle e₂ bk₂ hr₂ hop₂ hab₂
        (.op (.s .z) o₁ (.lit _ v₁) (.op .z o₂ (.lit _ v₂) M))) s₂)) s₁)
      (.app (.handle e₁ bk₁ hr₁ hop₁ hab₁ (.app (.handle e₂ bk₂ hr₂ hop₂ hab₂
        (.op .z o₂ (.lit _ v₂) (.op (.s .z) o₁ (.lit _ v₁) (M.ren (Ren.id _) Ren.swap)))) s₂)) s₁) := by
  apply soundness
  intro w hw η η' ρ ρ' hη hρ
  -- the outer handler, applied to its state
  refine CRU_arr.1 (handle_body_rel hw hη hρ ?_) w (W.le.refl w) _ _ (Val.fp s₁ hw hη hρ)
  intro i₁ i₁' hi₁ hi₁'
  have hw₁ := W.noPend_both hw i₁ i₁' hi₁ hi₁'
  have hs₁ := W.sub_both w i₁ i₁' hi₁ hi₁'
  have hη₁ : IR (w.both i₁ i₁' hi₁ hi₁') (η.cons (e := e₁) i₁) (η'.cons i₁') :=
    IR.cons (hη.sub hs₁) (W.both_r _ _ _ _ _) e₁
  -- the right-hand inner computation is related to itself
  have hR := CRU_F.1 (Cmp.fp (.app (.handle e₂ bk₂ hr₂ hop₂ hab₂
    (.op .z o₂ (.lit _ v₂) (.op (.s .z) o₁ (.lit _ v₁) (M.ren (Ren.id _) Ren.swap)))) s₂)
    hw₁ hη₁ (hρ.mono hs₁))
  simp only [Cmp.den, CTy.nuA] at hR ⊢
  -- at every free name the left-hand inner tree is the right-hand one
  refine TreeRel.nu_congr hR (fun i₂ hi₂ => ?_)
  have hne : i₁ ≠ i₂ := by
    intro h; subst h; simp [W.both, W.link, upd] at hi₂
  simp only [IEnv.cons_z, IEnv.cons_s, Val.lit_den]
  refine writer_swap hne o₁ o₂ v₁ v₂ _ _ _ (fun k d => hP _ _ v₂ k d) _ _ (fun y₁ y₂ => ?_) _
  exact (Cmp.den_ren (Ren.id _) Ren.swap M _ _ _ _ (fun _ _ => rfl)
    (fun B z => by rcases z with _ | _ | z <;> rfl)).symm

end EffRel
