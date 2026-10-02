import EffModelRel.Compat

/-!
# EffModelRel — the fundamental property

Every term is related to itself: `Cmp.fp`. The proof is one compatibility lemma per former,
by structural recursion on the term. The instance-relevant cases are where parametricity in
instances lives:

- `handle` and `nu` allocate on both sides and match the names (`nuA_both`);
- a handler catches an operation on the left exactly when it does on the right, because the
  world's matching is a bijection (`hnd_rel`);
- `ieq` answers the same on both sides for the same reason.
-/

namespace EffRel

variable {S : Sig}

theorem IR.sub {w w' : W} (h : w.sub w') {η η' : IEnv (S := S) Ψ} (hη : IR w η η') :
    IR w' η η' := hη.mono (fun _ _ hr => h.r' hr)

theorem IR.nil (w : W) : IR (S := S) (Ψ := []) w IEnv.nil IEnv.nil := fun _ x => nomatch x

theorem ER.nil (w : W) : ER (S := S) (Γ := []) w Env.nil Env.nil := fun _ x => nomatch x

theorem TreeRel.mapR' {R R' : W → X → X → Prop}
    (hR : ∀ w x x', w.noPend → R w x x' → R' w x x')
    {w : W} {t t' : Tree S X} (h : TreeRel R w t t') : TreeRel R' w t t' := by
  induction h with
  | ret hp hx => exact .ret hp (hR _ _ _ hp hx)
  | op hp hi hd _ ih => exact .op hp hi hd ih
  | ab hp hi hd => exact .ab hp hi hd
  | abE hp hi hd hf => exact .abE hp hi hd hf
  | act ha _ ih => exact .act ha ih
  | nu _ ih => exact .nu ih
  | nuL _ ih => exact .nuL ih
  | nuR _ ih => exact .nuR ih
  | gL _ ih => exact .gL ih
  | gR _ ih => exact .gR ih
  | mL hi' _ ih => exact .mL hi' ih
  | mR hi _ ih => exact .mR hi ih

theorem TreeRel.monoV {A : VTy S} {w w' : W} {t t' : Tree S A.den}
    (h : TreeRel (fun w a a' => VR A w a a') w t t') (hw : w.le w') :
    TreeRel (fun w a a' => VR A w a a') w' t t' :=
  TreeRel.mono (R := fun w a a' => VR A w a a') (fun _ _ _ _ h1 h2 => VR.mono A h1.sub h2) h w' hw

theorem StrmRel.monoV {A : VTy S} {w w' : W} {s s' : Strm S A.den}
    (h : StrmRel (fun w a a' => VR A w a a') w s s') (hw : w.le w') :
    StrmRel (fun w a a' => VR A w a a') w' s s' :=
  StrmRel.mono (RA := fun w a a' => VR A w a a') (fun _ _ _ _ h1 h2 => VR.mono A h1.sub h2) h w' hw

/-- The continuation a clause receives is related when its resumptions are. -/
theorem mkK_rel {q : Mode} {b : Rw} {r : G} {C : CTy S} {w : W} (hw : w.noPend)
    {k k' : r.den → C.den} (hk : ∀ y, CRU C w (k y) (k' y)) {t t' : Tree S Unit}
    (ht : TreeRel (fun w a a' => VR (S := S) (.g .unit) w a a') w t t') :
    VR (kty q b r C) w (mkK q.w q b r C k t) (mkK q.w q b r C k' t') := by
  have harr : CRU (.arr (.g r) b C) w k k' := CRU_arr.2 (fun w' hle y y' hy => by
    have hy' : y = y' := VR_g.1 hy
    subst hy'; exact CRU.mono C hle (hk y))
  unfold kty
  cases q.w with
  | true => exact (VR_U_noPend hw).2 (CRU_wth.2 ⟨harr, CRU_F.2 ht⟩)
  | false => exact (VR_U_noPend hw).2 harr

theorem dtorsT_rel {w : W} (hw : w.noPend) {d d' : List Dtor} (hd : DR w d d') :
    TreeRel (S := S) (fun w a a' => VR (S := S) (.g .unit) w a a') w (dtorsT d) (dtorsT d') :=
  dtors_rel hd (.ret hw (VR_g.2 rfl))

/-- A co-operation's answer is ground: related means equal. -/
theorem VR_coRes {e : S.E} {s : G} {o : S.O e} {w : W} {x x' : (coRes S e s o).den}
    (h : VR (coRes S e s o) w x x') : x = x' := by
  unfold coRes at x x' h
  rcases x with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases x' with ⟨a', b'⟩ | ⟨a', b'⟩ <;> simp only [VR] at h
  · obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl
  · obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl

theorem le_trans_gcP {w w' : W} (hw : w.noPend) (h : w.le w') : w.gcP.le w' :=
  W.le.trans (W.gcP_le w hw) h

mutual
theorem Val.fp : (v : Val S Ψ Γ A) → ∀ {w : W}, w.noPend → ∀ {η η' : IEnv Ψ} {ρ ρ' : Env Γ},
    IR w η η' → ER w ρ ρ' → VR A w (v.den η ρ) (v.den η' ρ')
  | .var x, _, _, _, _, _, _, _, hρ => hρ _ x
  | .unit, _, _, _, _, _, _, _, _ => VR_g.2 rfl
  | .int _, _, _, _, _, _, _, _, _ => VR_g.2 rfl
  | .bool _, _, _, _, _, _, _, _, _ => VR_g.2 rfl
  | .pair a b, _, hw, _, _, _, _, hη, hρ => VR_prod.2 ⟨Val.fp a hw hη hρ, Val.fp b hw hη hρ⟩
  | .inl a, _, hw, _, _, _, _, hη, hρ => VR_inl.2 (Val.fp a hw hη hρ)
  | .inr b, _, hw, _, _, _, _, hη, hρ => VR_inr.2 (Val.fp b hw hη hρ)
  | .thunk _ M, _, hw, _, _, _, _, hη, hρ => (VR_U_noPend hw).2 (Cmp.fp M hw hη hρ)
  | .fold (A := A) (b := b) v, w, hw, η, η', ρ, ρ', hη, hρ => by
      have h0 := CRU_wth.1 ((VR_U_noPend hw).1 (Val.fp v hw hη hρ))
      have h : TreeRel (fun w a a' => VR (A.step b) w a a') w (v.den η ρ).1 (v.den η' ρ').1 ∧
          TreeRel (fun w a a' => VR (S := S) (.g .unit) w a a') w (v.den η ρ).2 (v.den η' ρ').2 :=
        ⟨CRU_F.1 h0.1, CRU_F.1 h0.2⟩
      simp only [Val.den]
      refine VR_strm.2 ?_
      apply StrmRel.intro
      · refine TreeRel.mapR' (fun w₁ x x' hp₁ hx => ?_) (h.1.monoV (W.le_gcP w hw))
        rcases x with a | ⟨n, s⟩ <;> rcases x' with a' | ⟨n', s'⟩
        · exact VR_inl.1 hx
        · exact VR_inl_inr hx
        · exact VR_inr_inl hx
        · simp only [VR] at hx
          exact ⟨hx.1, hx.2.monoV (W.gcP_le w₁ hp₁)⟩
      · exact (h.2.monoV (W.le_gcP w hw)).mapR (fun _ _ _ _ => trivial)

theorem Cmp.fp : (M : Cmp S Ψ Γ C) → ∀ {w : W}, w.noPend → ∀ {η η' : IEnv Ψ} {ρ ρ' : Env Γ},
    IR w η η' → ER w ρ ρ' → CRU C w (M.den η ρ) (M.den η' ρ')
  | .ret v, _, hw, _, _, _, _, hη, hρ => CRU_F.2 (.ret hw (Val.fp v hw hη hρ))
  | .bind (C := C) M N, _, hw, _, _, _, _, hη, hρ =>
      bindC_rel C (CRU_F.1 (Cmp.fp M hw hη hρ)) (fun _ hs hp x x' hx =>
        Cmp.fp N hp (hη.sub hs) (ER.cons (hρ.mono hs) hx))
  | .lam M, _, hw, _, _, _, _, hη, hρ => CRU_arr.2 (fun _ hle a a' ha =>
      Cmp.fp M (hle.noPend' hw) (hη.mono hle.r) (ER.cons (hρ.mono hle.sub) ha))
  | .app M v, w, hw, _, _, _, _, hη, hρ =>
      CRU_arr.1 (Cmp.fp M hw hη hρ) w (W.le.refl w) _ _ (Val.fp v hw hη hρ)
  | .force v, _, hw, _, _, _, _, hη, hρ => (VR_U_noPend hw).1 (Val.fp v hw hη hρ)
  | .rcd M N, _, hw, _, _, _, _, hη, hρ => CRU_wth.2 ⟨Cmp.fp M hw hη hρ, Cmp.fp N hw hη hρ⟩
  | .prj1 M, _, hw, _, _, _, _, hη, hρ => (CRU_wth.1 (Cmp.fp M hw hη hρ)).1
  | .prj2 M, _, hw, _, _, _, _, hη, hρ => (CRU_wth.1 (Cmp.fp M hw hη hρ)).2
  | .split v M, _, hw, _, _, _, _, hη, hρ => by
      have hv := VR_prod.1 (Val.fp v hw hη hρ)
      exact Cmp.fp M hw hη (ER.cons (ER.cons hρ hv.1) hv.2)
  | .case (A := A) (B := B) v M N, _, hw, η, η', ρ, ρ', hη, hρ => by
      have hv := Val.fp v hw hη hρ
      simp only [Cmp.den]
      generalize v.den η ρ = x at hv ⊢
      generalize v.den η' ρ' = x' at hv ⊢
      rcases x with a | b <;> rcases x' with a' | b'
      · exact Cmp.fp M hw hη (ER.cons hρ (VR_inl.1 hv))
      · exact (VR_inl_inr hv).elim
      · exact (VR_inr_inl hv).elim
      · exact Cmp.fp N hw hη (ER.cons hρ (VR_inr.1 hv))
  | .ite v M N, _, hw, η, η', ρ, ρ', hη, hρ => by
      have hv := VR_g.1 (Val.fp v hw hη hρ)
      simp only [Cmp.den]
      rw [← hv]
      cases (v.den η ρ : Bool)
      · exact Cmp.fp N hw hη hρ
      · exact Cmp.fp M hw hη hρ
  | .absurd v, _, _, η, _, ρ, _, _, _ => (v.den η ρ : Empty).elim
  | .prim p a b, _, hw, _, _, _, _, hη, hρ => by
      have ha := VR_g.1 (Val.fp a hw hη hρ)
      have hb := VR_g.1 (Val.fp b hw hη hρ)
      simp only [Cmp.den]
      rw [ha, hb]
      exact CRU_F.2 (.ret hw (VR_g.2 rfl))
  | .emit v, _, hw, _, _, _, _, hη, hρ => by
      have hv := VR_g.1 (Val.fp v hw hη hρ)
      simp only [Cmp.den]
      rw [hv]
      exact CRU_F.2 (.act .out (fun _ => .ret hw (VR_g.2 rfl)))
  | .op (C := C) x o v M, _, hw, _, _, _, _, hη, hρ => by
      have hv := VR_g.1 (Val.fp v hw hη hρ)
      simp only [Cmp.den]
      rw [hv]
      exact opA_rel C hw (hη _ x) .nil (fun y => Cmp.fp M hw hη (ER.cons hρ (VR_g.2 rfl)))
  | .ab (C := C) x a v, _, hw, _, _, _, _, hη, hρ => by
      have hv := VR_g.1 (Val.fp v hw hη hρ)
      simp only [Cmp.den]
      rw [hv]
      exact abA_rel C hw (hη _ x) .nil
  | .handle (C := C) e _ hr hop hab M, w, hw, η, η', ρ, ρ', hη, hρ => by
      simp only [Cmp.den]
      apply nuA_both C
      intro i i' hi hi'
      have hs := W.sub_both w i i' hi hi'
      apply hnd_rel C (CRU_F.1 (Cmp.fp M (W.noPend_both hw _ _ _ _)
        (IR.cons (hη.sub hs) (W.both_r _ _ _ _ _) e) (hρ.mono hs))) (W.both_r _ _ _ _ _)
      · intro w' h1 hp x x' hx
        exact Cmp.fp hr hp (hη.sub (hs.trans h1)) (ER.cons (hρ.mono (hs.trans h1)) hx)
      · intro w' h1 hp o v k k' d d' hk hd
        exact Cmp.fp (hop o) hp (hη.sub (hs.trans h1))
          (ER.cons (ER.cons (hρ.mono (hs.trans h1)) (VR_g.2 rfl)) (mkK_rel hp hk (dtorsT_rel hp hd)))
      · intro w' h1 hp a v
        exact Cmp.fp (hab a) hp (hη.sub (hs.trans h1)) (ER.cons (hρ.mono (hs.trans h1)) (VR_g.2 rfl))
  | .handleAt (C := C) x _ hr hop hab M, w, hw, η, η', ρ, ρ', hη, hρ => by
      simp only [Cmp.den]
      apply hnd_rel C (CRU_F.1 (Cmp.fp M hw hη hρ)) (hη _ x)
      · intro w' h1 hp x x' hx
        exact Cmp.fp hr hp (hη.sub h1) (ER.cons (hρ.mono h1) hx)
      · intro w' h1 hp o v k k' d d' hk hd
        exact Cmp.fp (hop o) hp (hη.sub h1)
          (ER.cons (ER.cons (hρ.mono h1) (VR_g.2 rfl)) (mkK_rel hp hk (dtorsT_rel hp hd)))
      · intro w' h1 hp a v
        exact Cmp.fp (hab a) hp (hη.sub h1) (ER.cons (hρ.mono h1) (VR_g.2 rfl))
  | .nu (C := C) e M, w, hw, _, _, _, _, hη, hρ => by
      simp only [Cmp.den]
      exact nuA_both C (fun i i' hi hi' => Cmp.fp M (W.noPend_both hw _ _ _ _)
        (IR.cons (hη.sub (W.sub_both _ _ _ _ _)) (W.both_r _ _ _ _ _) e)
        (hρ.mono (W.sub_both _ _ _ _ _)))
  | .ieq x y, w, hw, η, η', _, _, hη, _ => by
      simp only [Cmp.den]
      have : decide (η _ x = η _ y) = decide (η' _ x = η' _ y) := by
        rw [decide_eq_decide]; exact (w.r_iff (hη _ y) (hη _ x))
      rw [this]
      exact CRU_F.2 (.ret hw (VR_g.2 rfl))
  | .ilam (e := e) M, _, hw, _, _, _, _, hη, hρ => CRU_pi.2 (fun _ hle i i' hi =>
      Cmp.fp M (hle.noPend' hw) (IR.cons (hη.mono hle.r) hi e) (hρ.mono hle.sub))
  | .iapp M x, w, hw, _, _, _, _, hη, hρ =>
      CRU_pi.1 (Cmp.fp M hw hη hρ) w (W.le.refl w) _ _ (hη _ x)
  | .newcap e s co v, w, hw, η, η', ρ, ρ', hη, hρ => by
      have hv := VR_g.1 (Val.fp v hw hη hρ)
      simp only [Cmp.den]
      rw [hv]
      apply CRU_F.2
      apply TreeRel.nu
      intro c c' hc hc'
      refine .act (.new (W.both_r _ _ _ _ _)) (fun _ => .ret (W.noPend_both hw _ _ _ _) ?_)
      refine VR_cap.2 ⟨W.both_r _ _ _ _ _, fun w' hle o a st => ?_⟩
      have hp' : w'.noPend := hle.noPend' (W.gcP_noPend _)
      exact (CRU_F.1 (Cmp.fp (co o) hp' (IR.nil _)
        (ER.cons (ER.cons (ER.nil _) (VR_g.2 rfl)) (VR_g.2 rfl)))).mapR
        (fun _ _ _ h => VR_coRes h)
  | .getcap v, _, hw, _, _, _, _, hη, hρ => by
      have hv := (VR_cap.1 (Val.fp v hw hη hρ)).1
      simp only [Cmp.den]
      exact CRU_F.2 (.act (.kill hv) (fun _ => .ret hw (VR_g.2 rfl)))
  | .lend (A := A) (e := e) (s := sg) v M, w, hw, η, η', ρ, ρ', hη, hρ => by
      have hvv := Val.fp v hw hη hρ
      have hv := VR_cap.1 hvv
      simp only [Cmp.den]
      apply CRU_F.2
      refine .act (.rd hv.1) (fun st => .nu (fun i i' hi hi' => ?_))
      have hs := W.sub_both w i i' hi hi'
      refine Tree.bind_rel (R1 := fun w a a' => VR (.sum A (.g .int)) w a a') ?_ ?_
      · refine runL_rel (R := fun w a a' => VR A w a a')
          (R2 := fun w a a' => VR (.sum A (.g .int)) w a a')
          (fun _ _ _ _ h1 h2 => VR.mono _ h1.sub h2)
          (fun _ _ _ h => VR_inl.2 h) (fun _ _ => VR_inr.2 (VR_g.2 rfl))
          (CRU_F.1 (Cmp.fp M (W.noPend_both hw _ _ _ _)
            (IR.cons (hη.sub hs) (W.both_r _ _ _ _ _) _) (hρ.mono hs)))
          (W.both_r _ _ _ _ _) (hs.r' hv.1) ?_ st
        intro w' h1 hp o a st'
        exact hv.2 w' (le_trans_gcP hw (W.noPend_le_of_sub hw hp (hs.trans h1))) o a st'
      · intro w₂ h₂ hp₂ z z' hz
        exact .ret hp₂ (VR_prod.2 ⟨VR.mono (.cap e sg) (hs.trans h₂) hvv, hz⟩)
  | .using ℓ M, w, hw, η, η', ρ, ρ', hη, hρ => by
      simp only [Cmp.den]
      apply CRU_F.2
      refine .nu (fun r r' hr hr' => .act (.acq (W.both_r _ _ _ _ _)) (fun _ => ?_))
      have hs := W.sub_both w r r' hr hr'
      exact addFin_rel (CRU_F.1 (Cmp.fp M (W.noPend_both hw _ _ _ _)
        (IR.cons (hη.sub hs) (W.both_r _ _ _ _ _) _) (hρ.mono hs)))
        (W.both_r _ _ _ _ _)
  | .unfold (A := A) (b := b) v, w, hw, η, η', ρ, ρ', hη, hρ => by
      have hv := VR_strm.1 (Val.fp v hw hη hρ)
      simp only [Cmp.den]
      generalize v.den η ρ = s at hv ⊢
      generalize v.den η' ρ' = s' at hv ⊢
      rcases s with ⟨p, d⟩; rcases s' with ⟨p', d'⟩
      have h := hv.elim
      simp only
      refine CRU_wth.2 ⟨CRU_F.2 ?_, CRU_F.2 ?_⟩
      · refine (TreeRel.mapR' (R' := fun w a a' => VR (A.step b) w a a')
          (fun w₁ x x' hp₁ hx => ?_) h.1).monoV (W.gcP_le w hw)
        rcases x with a | ⟨n, s⟩ <;> rcases x' with a' | ⟨n', s'⟩
        · exact VR_inl.2 hx
        · exact hx.elim
        · exact hx.elim
        · simp only [VR]
          exact ⟨hx.1, hx.2.monoV (W.le_gcP w₁ hp₁)⟩
      · exact (h.2.mapR' (R' := fun w a a' => VR (S := S) (.g .unit) w a a')
          (fun _ _ _ hp _ => VR_g.2 rfl)).monoV (W.gcP_le w hw)
  | .bfix (C := C) x a v n M, w, hw, η, η', ρ, ρ', hη, hρ => by
      have hv := VR_g.1 (Val.fp v hw hη hρ)
      simp only [Cmp.den]
      rw [hv]
      induction n with
      | zero => exact abA_rel C hw (hη _ x) .nil
      | succ n ih => exact Cmp.fp M hw hη (ER.cons hρ ((VR_U_noPend hw).2 ih))
end

/-- The fundamental property: every term is logically related to itself. -/
theorem fundamental (M : Cmp S Ψ Γ C) : LR M M :=
  fun _ hw _ _ _ _ hη hρ => Cmp.fp M hw hη hρ

end EffRel
