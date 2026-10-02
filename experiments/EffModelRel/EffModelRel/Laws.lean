import EffModelRel.Rename

/-!
# EffModelRel — the laws, as theorems

Every law is a contextual equivalence (`CtxEq`), proved through the logical relation
(`soundness`). Laws that are equalities of denotations need nothing more (`CtxEq.of_den`); the
instance laws need the relation's treatment of names.

- **L1a, algebraicity**, at `to`, at function, record and instance-abstraction types, and at
  arity 0, including the destructor form `K[raise] ≡ D_K; raise`.
- **L2, the handler laws**: return, operation, forwarding (resuming and abortive).
- **L6, Staton's instance laws**: `idem-ν`, `ν/ν`, `new-ν`; and **no accidental handling** as
  parametricity in instances. `ν/op` is not proved (see `docs/effect-model.md`).
-/

namespace EffRel

variable {S : Sig}

/-! ## Freshness -/

/-- A name the world has not allocated differs from every instance a related environment names. -/
theorem fresh_of_free {w : W} {η η' : IEnv (S := S) Ψ} (hη : IR w η η') {i : Nat}
    (hi : w.sl i = .free) : ∀ e (x : Var Ψ e), η e x ≠ i := fun e x hx => by
  have h1 := hη e x; rw [hx] at h1; unfold W.r at h1; rw [hi] at h1; cases h1

/-- Two `ν`s whose bodies agree on every fresh name are related. -/
theorem LR.nu_of_fresh {e : S.E} {M N : Cmp S (e :: Ψ) Γ C}
    (h : ∀ (η : IEnv Ψ) ρ i, (∀ e' (x : Var Ψ e'), η e' x ≠ i) →
      M.den (η.cons i) ρ = N.den (η.cons i) ρ) :
    LR (Cmp.nu e M) (Cmp.nu e N) := by
  intro w hw η η' ρ ρ' hη hρ
  simp only [Cmp.den]
  apply nuA_both C
  intro i i' hi hi'
  rw [h η ρ i (fresh_of_free hη hi)]
  have hs := W.sub_both w i i' hi hi'
  exact Cmp.fp N (W.noPend_both hw _ _ _ _) (IR.cons (hη.sub hs) (W.both_r _ _ _ _ _) e)
    (hρ.mono hs)

/-- A `ν` whose body, on every fresh name, is a term that does not use it. -/
theorem LR.nuG_of {e : S.E} {M : Cmp S (e :: Ψ) Γ C} {N : Cmp S Ψ Γ C}
    (h : ∀ (η : IEnv Ψ) ρ i, (∀ e' (x : Var Ψ e'), η e' x ≠ i) → M.den (η.cons i) ρ = N.den η ρ) :
    LR (Cmp.nu e M) N := by
  intro w hw η η' ρ ρ' hη hρ
  simp only [Cmp.den]
  apply nuA_gL C
  intro i hi
  rw [h η ρ i (fresh_of_free hη hi)]
  have hs := W.sub_garbL w i hi
  exact Cmp.fp N (W.noPend_garbL hw _ _) (hη.sub hs) (hρ.mono hs)

theorem wk_lift_pt {A B : VTy S} {ρ : Env (S := S) Γ} (a : A.den) (b : B.den) :
    ∀ D x, ((ρ.cons b).cons a) D (Ren.wk.lift D x) = (ρ.cons a) D x := by
  intro D x; cases x <;> rfl

theorem TreeRel.of_eq {R : W → X → X → Prop} {w : W} {t₁ t₂ t' : Tree S X} (h : t₁ = t₂)
    (h' : TreeRel R w t₂ t') : TreeRel R w t₁ t' := h ▸ h'

theorem TreeRel.of_eq' {R : W → X → X → Prop} {w : W} {t t₁' t₂' : Tree S X} (h : t₁' = t₂')
    (h' : TreeRel R w t t₂') : TreeRel R w t t₁' := h ▸ h'

/-! ## L1a: algebraicity -/

/-- At `to`: `(op; y.M) to z. N ≡ op; y.(M to z. N)`. -/
theorem alg_bind {e : S.E} (x : Var Ψ e) (o : S.O e) (v : Val S Ψ Γ (.g (S.arg e o)))
    (M : Cmp S Ψ (.g (S.res e o) :: Γ) (.F A)) (N : Cmp S Ψ (A :: Γ) C) :
    CtxEq (.bind (.op x o v M) N) (.op x o v (.bind M (N.ren (Ren.id Ψ) Ren.wk.lift))) := by
  apply CtxEq.of_den; intro η ρ
  simp only [Cmp.den, CTy.opA, Tree.bindC]
  congr 1; funext y; congr 1; funext a
  exact (Cmp.den_ren _ _ N _ _ _ _ (fun _ _ => rfl) (wk_lift_pt (B := .g _) a y)).symm

/-- At a function type: `(op; y.M) w ≡ op; y.(M w)`. -/
theorem alg_app {e : S.E} (x : Var Ψ e) (o : S.O e) (v : Val S Ψ Γ (.g (S.arg e o)))
    (M : Cmp S Ψ (.g (S.res e o) :: Γ) (.arr A b C)) (u : Val S Ψ Γ A) :
    CtxEq (.app (.op x o v M) u) (.op x o v (.app M u.wk)) := by
  apply CtxEq.of_den; intro η ρ
  simp only [Cmp.den, CTy.opA]
  congr 1; funext y
  exact congrArg (M.den η (ρ.cons (VTy.gv y))) (Val.den_wk u η ρ (VTy.gv y)).symm

/-- At a record type: `π₁ (op; y.M) ≡ op; y.(π₁ M)`, and the same for `π₂`. -/
theorem alg_prj1 {e : S.E} (x : Var Ψ e) (o : S.O e) (v : Val S Ψ Γ (.g (S.arg e o)))
    (M : Cmp S Ψ (.g (S.res e o) :: Γ) (.wth C D)) :
    CtxEq (.prj1 (.op x o v M)) (.op x o v (.prj1 M)) := by
  apply CtxEq.of_den; intro η ρ; simp only [Cmp.den, CTy.opA]

theorem alg_prj2 {e : S.E} (x : Var Ψ e) (o : S.O e) (v : Val S Ψ Γ (.g (S.arg e o)))
    (M : Cmp S Ψ (.g (S.res e o) :: Γ) (.wth C D)) :
    CtxEq (.prj2 (.op x o v M)) (.op x o v (.prj2 M)) := by
  apply CtxEq.of_den; intro η ρ; simp only [Cmp.den, CTy.opA]

/-- At an instance abstraction. -/
theorem alg_iapp {e e' : S.E} (x : Var Ψ e) (o : S.O e) (v : Val S Ψ Γ (.g (S.arg e o)))
    (M : Cmp S Ψ (.g (S.res e o) :: Γ) (.pi e' C)) (z : Var Ψ e') :
    CtxEq (.iapp (.op x o v M) z) (.op x o v (.iapp M z)) := by
  apply CtxEq.of_den; intro η ρ; simp only [Cmp.den, CTy.opA]

/-- At arity 0: `raise to z. N ≡ raise`. -/
theorem alg_ab_bind {e : S.E} (x : Var Ψ e) (a : S.A e) (v : Val S Ψ Γ (.g (S.aarg e a)))
    (N : Cmp S Ψ (A :: Γ) C) : CtxEq (.bind (.ab (C := .F A) x a v) N) (.ab x a v) := by
  apply CtxEq.of_den; intro η ρ; simp only [Cmp.den, CTy.abA, Tree.bindC]

/-- At arity 0, at a function type: `raise w ≡ raise`. -/
theorem alg_ab_app {e : S.E} (x : Var Ψ e) (a : S.A e) (v : Val S Ψ Γ (.g (S.aarg e a)))
    (u : Val S Ψ Γ A) : CtxEq (.app (.ab (C := .arr A b C) x a v) u) (.ab x a v) := by
  apply CtxEq.of_den; intro η ρ; simp only [Cmp.den, CTy.abA]

/-- **The destructor form at arity 0**: `K[raise] ≡ D_K; raise`, for `K` a destructor frame
around a sequencing frame. The left aborts carrying the frame's destructor, which its handler
runs; the right runs it first. -/
theorem alg_dtor {e : S.E} (ℓ : Nat) (x : Var Ψ e) (a : S.A e) (v : Val S Ψ Γ (.g (S.aarg e a)))
    (N : Cmp S Ψ (B :: .res :: Γ) (.F A)) :
    CtxEq (.using ℓ (.bind (.ab x a v.wk) N))
      (.bind (.using ℓ (.ret .unit)) (.ab (C := .F A) x a v.wk)) := by
  apply soundness
  intro w hw η η' ρ ρ' hη hρ
  have hv := VR_g.1 (Val.fp v hw hη hρ)
  simp only [Cmp.den, CTy.abA, CTy.nuA, CTy.actA, Tree.bindC, Tree.addFin]
  apply CRU_F.2
  refine .nu (fun r r' hr hr' => .act (.acq (W.both_r _ _ _ _ _)) (fun _ => ?_))
  refine TreeRel.of_eq (congrArg (fun z => Tree.ab (η e x) e a z ([] ++ [Dtor.free ℓ r]))
    ((Val.den_wk v η ρ (VTy.resv ℓ r)).trans hv)) ?_
  refine TreeRel.of_eq' (congrArg (fun z => Tree.act (Act.free ℓ r') (fun _ => Tree.ab (η' e x) e a z []))
    (Val.den_wk v η' ρ' _)) ?_
  exact TreeRel.abE (d := [Dtor.free ℓ r]) (d' := [Dtor.free ℓ r']) (f := []) (f' := [])
    (W.noPend_both hw _ _ _ _) ((W.sub_both _ _ _ _ _).r' (hη _ x))
    (.cons (.free (W.both_r _ _ _ _ _)) .nil) .nil

/-! ## L2: the handler laws -/

/-- The continuation as a value: a thunk of `resume` (and of a `cancel` that runs nothing, when
the operation may drop it). -/
def kVal {r : G} {C : CTy S} : (w : Bool) → (q : Mode) → (b : Eb) → Cmp S Ψ (.g r :: Γ) C →
    Val S Ψ Γ (ktyB w q b r C)
  | true, _, _, M => .thunk _ (.rcd (.lam M) (.ret .unit))
  | false, q, _, M => .thunk q (.lam M)

theorem kVal_den {r : G} {C : CTy S} (w : Bool) (q : Mode) (b : Eb) (M : Cmp S Ψ (.g r :: Γ) C)
    (η : IEnv Ψ) (ρ : Env Γ) :
    (kVal w q b M).den η ρ = mkK w q b r C (fun y => M.den η (ρ.cons (VTy.gv y))) (Tree.ret ()) := by
  cases w <;> rfl

/-- **H-ret**: `handle (return v) ≡ h_ret v`. -/
theorem h_ret (e : S.E) (hr : Cmp S Ψ (A :: Γ) C)
    (hop : (o : S.O e) → Cmp S Ψ (kty (S.q e o) b (S.res e o) C :: .g (S.arg e o) :: Γ) C)
    (hab : (a : S.A e) → Cmp S Ψ (.g (S.aarg e a) :: Γ) C) (v : Val S Ψ Γ A) :
    CtxEq (.handle e b hr hop hab (.ret (v.ren Ren.wk (Ren.id Γ)))) (.bind (.ret v) hr) := by
  apply soundness
  intro w hw η η' ρ ρ' hη hρ
  simp only [Cmp.den, Tree.hnd, Tree.bindC]
  apply nuA_gL C
  intro i hi
  rw [Val.den_ren Ren.wk (Ren.id Γ) v (η.cons i) η ρ ρ (fun _ _ => rfl) (fun _ _ => rfl)]
  have hs := W.sub_garbL w i hi
  exact Cmp.fp hr (W.noPend_garbL hw _ _) (hη.sub hs) (ER.cons (hρ.mono hs)
    (VR.mono _ hs (Val.fp v hw hη hρ)))

/-- **H-op**: `handle (op_h v; y.M) ≡ h_op(v, λy. handle M)`. The handler is at an instance
variable, so the continuation can name it. -/
theorem h_op {e : S.E} (x : Var Ψ e) (hr : Cmp S Ψ (A :: Γ) C)
    (hop : (o : S.O e) → Cmp S Ψ (kty (S.q e o) b (S.res e o) C :: .g (S.arg e o) :: Γ) C)
    (hab : (a : S.A e) → Cmp S Ψ (.g (S.aarg e a) :: Γ) C) (o : S.O e)
    (v : Val S Ψ Γ (.g (S.arg e o))) (M : Cmp S Ψ (.g (S.res e o) :: Γ) (.F A)) :
    CtxEq (.handleAt x b hr hop hab (.op x o v M))
      (.bind (.ret v) (.bind (.ret (kVal (S.q e o).w (S.q e o) b
          ((Cmp.handleAt x b (hr.ren (Ren.id Ψ) Ren.wk.lift)
              (fun o' => (hop o').ren (Ren.id Ψ) Ren.wk.lift.lift)
              (fun a => (hab a).ren (Ren.id Ψ) Ren.wk.lift) M).ren (Ren.id Ψ) Ren.wk.lift)))
        (hop o))) := by
  apply CtxEq.of_den; intro η ρ
  simp only [Cmp.den, CTy.opA, Tree.bindC]
  rw [kVal_den]
  simp only [Tree.hnd, ↓reduceIte]
  refine (catchOp_self _ _ _ _ _ _ _).trans ?_
  congr 1; congr 1; congr 1; funext y
  refine Eq.trans ?_ (Cmp.den_ren (Ren.id Ψ) Ren.wk.lift _ η η _ (ρ.cons (A := .g _) y)
    (fun _ _ => rfl) (wk_lift_pt (A := .g _) (B := .g _) y _)).symm
  simp only [Cmp.den]
  congr 1
  · funext a'
    exact (Cmp.den_ren _ _ hr η η _ _ (fun _ _ => rfl) (wk_lift_pt (B := .g _) a' y)).symm
  · funext o' v' k' d'
    exact (Cmp.den_ren _ _ (hop o') η η _ _ (fun _ _ => rfl)
      (fun D z => by rcases z with _ | _ | z <;> rfl)).symm
  · funext a' v'
    exact (Cmp.den_ren _ _ (hab a') η η _ _ (fun _ _ => rfl)
      (wk_lift_pt (A := .g _) (B := .g _) v' y)).symm

def Val.wkI (v : Val S Ψ Γ A) : Val S (e :: Ψ) Γ A := v.ren Ren.wk (Ren.id Γ)

theorem Val.den_wkI (v : Val S Ψ Γ A) (η : IEnv Ψ) (ρ : Env Γ) (i : Nat) :
    (v.wkI (e := e)).den (η.cons i) ρ = v.den η ρ :=
  Val.den_ren _ _ v _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

/-- **H-fwd**: a handler passes on an operation of another instance:
`ν h. handle_h (op_l v; y.M) ≡ ν h. op_l v; y. handle_h M`. The instance `h` is fresh, so `l`
cannot be it. -/
theorem h_fwd {e e' : S.E} (x : Var Ψ e') (hr : Cmp S (e :: Ψ) (A :: Γ) C)
    (hop : (o : S.O e) → Cmp S (e :: Ψ) (kty (S.q e o) b (S.res e o) C :: .g (S.arg e o) :: Γ) C)
    (hab : (a : S.A e) → Cmp S (e :: Ψ) (.g (S.aarg e a) :: Γ) C) (o : S.O e')
    (v : Val S (e :: Ψ) Γ (.g (S.arg e' o))) (M : Cmp S (e :: Ψ) (.g (S.res e' o) :: Γ) (.F A)) :
    CtxEq (.nu e (.handleAt .z b hr hop hab (.op (.s x) o v M)))
      (.nu e (.op (.s x) o v (.handleAt .z b (hr.ren (Ren.id _) Ren.wk.lift)
        (fun o' => (hop o').ren (Ren.id _) Ren.wk.lift.lift)
        (fun a => (hab a).ren (Ren.id _) Ren.wk.lift) M))) := by
  apply soundness
  apply LR.nu_of_fresh
  intro η ρ i hf
  simp only [Cmp.den, CTy.opA, Tree.hnd]
  refine (if_neg (hf e' x)).trans ?_
  congr 1; funext y
  congr 1
  · funext a'
    exact (Cmp.den_ren _ _ hr _ _ _ _ (fun _ _ => rfl) (wk_lift_pt (B := .g _) a' y)).symm
  · funext o' v' k' d'
    exact (Cmp.den_ren _ _ (hop o') _ _ _ _ (fun _ _ => rfl)
      (fun D z => by rcases z with _ | _ | z <;> rfl)).symm
  · funext a' v'
    exact (Cmp.den_ren _ _ (hab a') _ _ _ _ (fun _ _ => rfl)
      (wk_lift_pt (A := .g _) (B := .g _) v' y)).symm

/-- **H-fwd at arity 0**: `ν h. handle_h (raise_f) ≡ raise_f`. -/
theorem h_fwd_ab {e e' : S.E} (x : Var Ψ e') (hr : Cmp S (e :: Ψ) (A :: Γ) C)
    (hop : (o : S.O e) → Cmp S (e :: Ψ) (kty (S.q e o) b (S.res e o) C :: .g (S.arg e o) :: Γ) C)
    (hab : (a : S.A e) → Cmp S (e :: Ψ) (.g (S.aarg e a) :: Γ) C) (a : S.A e')
    (v : Val S Ψ Γ (.g (S.aarg e' a))) :
    CtxEq (.nu e (.handleAt .z b hr hop hab (.ab (C := .F A) (.s x) a v.wkI))) (.ab x a v) := by
  apply soundness
  apply LR.nuG_of
  intro η ρ i hf
  simp only [Cmp.den, CTy.abA, Tree.hnd]
  refine (if_neg (hf e' x)).trans ?_
  rw [Val.den_wkI]; rfl

/-! ## L6: Staton's instance laws -/

/-- **idem-ν**: an unused instance is unobservable. -/
theorem idem_nu (e : S.E) (M : Cmp S Ψ Γ C) : CtxEq (.nu e M.wkI) M :=
  soundness (LR.nuG_of fun η ρ i _ => Cmp.den_wkI M η ρ i)

/-- **new-ν**: a fresh instance differs from every existing one. -/
theorem new_nu {e e' : S.E} (a : Var Ψ e') (M N : Cmp S (e :: Ψ) Γ C) :
    CtxEq (.nu e (.bind (.ieq (.s a) .z) (.ite (.var .z) M.wk N.wk))) (.nu e N) := by
  apply soundness
  apply LR.nu_of_fresh
  intro η ρ i hf
  simp only [Cmp.den, Tree.bindC, Val.den]
  have : decide (η e' a = i) = false := decide_eq_false (hf e' a)
  simp only [IEnv.cons, Env.cons, this]
  exact Cmp.den_wk N _ _ _

theorem W.both_sl {w : W} {i i' : Nat} {hi hi'} (a : Nat) :
    (w.both i i' hi hi').sl a = upd w.sl i (.m i') a := rfl
theorem W.both_sr {w : W} {i i' : Nat} {hi hi'} (b : Nat) :
    (w.both i i' hi hi').sr b = upd w.sr i' (.m i) b := rfl

/-- **ν/ν**: the order in which two instances are allocated is unobservable. -/
theorem nu_nu (e : S.E) (M : Cmp S (e :: e :: Ψ) Γ C) :
    CtxEq (.nu e (.nu e M)) (.nu e (.nu e (M.ren Ren.swap (Ren.id Γ)))) := by
  apply soundness
  intro w hw η η' ρ ρ' hη hρ
  simp only [Cmp.den]
  apply nuA_L C; intro i₁ h₁
  apply nuA_R C; intro j₁ h₁'
  have hp₁ : ((w.pendL i₁ h₁).pendR j₁ h₁').sr j₁ = .p := by
    simp [W.pendR, W.setR, upd]
  apply nuA_mL C hp₁; intro i₂ h₂
  have hne₂ : i₂ ≠ i₁ := by
    intro h; subst h; simp [W.pendR, W.setR, W.pendL, W.setL, upd] at h₂
  have hp₂ : (((w.pendL i₁ h₁).pendR j₁ h₁').matchL i₂ j₁ h₂ hp₁).sl i₁ = .p := by
    simp [W.matchL, W.link, W.pendR, W.setR, W.pendL, W.setL, upd, Ne.symm hne₂]
  apply nuA_mR C hp₂; intro j₂ h₂'
  have hne₂' : j₂ ≠ j₁ := by
    intro h; subst h; simp [W.matchL, W.link, upd] at h₂'
  rw [Cmp.den_ren Ren.swap (Ren.id Γ) M _ ((η'.cons j₂).cons j₁) ρ' ρ'
    (fun e x => by rcases x with _ | _ | x <;> rfl) (fun _ _ => rfl)]
  have hs : w.sub ((((w.pendL i₁ h₁).pendR j₁ h₁').matchL i₂ j₁ h₂ hp₁).matchR j₂ i₁ h₂' hp₂) :=
    ((((W.sub_pendL _ _ _).trans (W.sub_pendR _ _ _)).trans (W.sub_matchL _ _ _ _ _)).trans
      (W.sub_matchR _ _ _ _ _))
  refine Cmp.fp M ⟨fun a => ?_, fun b => ?_⟩ ?_ (hρ.mono hs)
  · simp only [W.matchR, W.matchL, W.link, W.pendR, W.setR, W.pendL, W.setL, upd]
    by_cases ha1 : a = i₁
    · subst ha1; simp
    · by_cases ha2 : a = i₂
      · subst ha2; simp [ha1]
      · simp [ha1, ha2, hw.1 a]
  · simp only [W.matchR, W.matchL, W.link, W.pendR, W.setR, W.pendL, W.setL, upd]
    by_cases hb1 : b = j₂
    · subst hb1; simp
    · by_cases hb2 : b = j₁
      · subst hb2; simp [hb1]
      · simp [hb1, hb2, hw.2 b]
  · intro e' x
    rcases x with _ | _ | x
    · exact (W.sub_matchR _ _ _ _ _).r' (W.matchL_r _ _ _ _ _)
    · exact W.matchR_r _ _ _ _ _
    · exact hs.r' (hη _ x)

/-! ## No accidental handling, as parametricity in instances -/

theorem W.sl_link_ne {w : W} {i i' : Nat} {h1 h2} {a : Nat} (h : a ≠ i) :
    (w.link i i' h1 h2).sl a = w.sl a := upd_ne _ _ h
theorem W.sl_setL_ne {w : W} {i : Nat} {s : St} {hs h1} {a : Nat} (h : a ≠ i) :
    (w.setL i s hs h1).sl a = w.sl a := upd_ne _ _ h

/-- A handler of an instance the world never matched catches nothing: on related trees it is
the identity. -/
theorem hnd_transparent {A : VTy S} {R : W → A.den → A.den → Prop} {w : W}
    {t t' : Tree S A.den} (h : TreeRel R w t t') {i : Nat} {e : S.E}
    {hr : A.den → (CTy.F A).den} (hhr : ∀ x, hr x = Tree.ret x) {hop hab}
    (hi : w.sl i = .g) : TreeRel R w (t.hnd (.F A) i e hr hop hab) t' := by
  revert hi
  induction h with
  | ret hp hx => intro _; simp only [Tree.hnd, hhr]; exact .ret hp hx
  | @op w j j' e' o v k k' d d' hp hj hd _ ih =>
      intro hi
      have hji : j ≠ i := fun h' => by subst h'; unfold W.r at hj; rw [hj] at hi; cases hi
      simp only [Tree.hnd]; rw [if_neg hji]
      exact .op hp hj hd (fun y => ih y hi)
  | @ab w j j' e' a v d d' hp hj hd =>
      intro hi
      have hji : j ≠ i := fun h' => by subst h'; unfold W.r at hj; rw [hj] at hi; cases hi
      simp only [Tree.hnd]; rw [if_neg hji]
      exact .ab hp hj hd
  | @abE w j j' e' a v d d' f f' hp hj hd hf =>
      intro hi
      have hji : j ≠ i := fun h' => by subst h'; unfold W.r at hj; rw [hj] at hi; cases hi
      simp only [Tree.hnd]; rw [if_neg hji]
      exact .abE hp hj hd hf
  | act ha _ ih => intro hi; exact .act ha (fun y => ih y hi)
  | @nu w k k' _ ih =>
      intro hi
      exact .nu (fun j j' hj hj' => ih j j' hj hj' (
        (upd_ne _ _ (fun h' => by subst h'; rw [hj] at hi; cases hi)).trans hi))
  | @nuL w k t' _ ih =>
      intro hi
      exact .nuL (fun j hj => ih j hj (
        (upd_ne _ _ (fun h' => by subst h'; rw [hj] at hi; cases hi)).trans hi))
  | nuR _ ih => intro hi; exact .nuR (fun j hj => ih j hj hi)
  | @gL w k t' _ ih =>
      intro hi
      exact .gL (fun j hj => ih j hj (
        (upd_ne _ _ (fun h' => by subst h'; rw [hj] at hi; cases hi)).trans hi))
  | gR _ ih => intro hi; exact .gR (fun j hj => ih j hj hi)
  | @mL w k t' i' hi' _ ih =>
      intro hi
      exact .mL hi' (fun j hj => ih j hj (
        (upd_ne _ _ (fun h' => by subst h'; rw [hj] at hi; cases hi)).trans hi))
  | @mR w t k' j hj _ ih =>
      intro hi
      exact .mR hj (fun j' hj' => ih j' hj' (
        (upd_ne _ _ (fun h' => by subst h'; rw [hj] at hi; cases hi)).trans hi))

/-- **No accidental handling.** A handler of a fresh instance, around a computation that cannot
name it, is invisible: `ν h. handle_h M ≡ M` for any clauses. This is parametricity in
instances: `M` treats every instance it is not given alike, so it treats `h` as it treats an
instance the world never matches. -/
theorem no_accidental_handling (e : S.E)
    (hop : (o : S.O e) → Cmp S (e :: Ψ) (kty (S.q e o) b (S.res e o) (.F A) :: .g (S.arg e o) :: Γ)
      (.F A))
    (hab : (a : S.A e) → Cmp S (e :: Ψ) (.g (S.aarg e a) :: Γ) (.F A)) (M : Cmp S Ψ Γ (.F A)) :
    CtxEq (.nu e (.handleAt .z b (.ret (.var .z)) hop hab M.wkI)) M := by
  apply soundness
  intro w hw η η' ρ ρ' hη hρ
  simp only [Cmp.den, CTy.nuA]
  apply CRU_F.2
  refine .gL (fun i hi => ?_)
  rw [Cmp.den_wkI]
  have hs := W.le_garbL_self w i hi
  refine hnd_transparent (CRU_F.1 (CRU.mono _ hs (Cmp.fp M hw hη hρ))) (fun _ => rfl) ?_
  show upd w.sl i St.g i = St.g
  exact upd_same _ _ _

end EffRel
