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
    (M : Cmp S Ψ (.g (S.res e o) :: Γ) (.arr A C)) (u : Val S Ψ Γ A) :
    CtxEq (.app (.op x o v M) u) (.op x o v (.app M u.wk)) := by
  apply CtxEq.of_den; intro η ρ
  simp only [Cmp.den, CTy.opA]
  congr 1; funext y
  rw [Val.den_wk (A := .g _) u η ρ y]

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
    (u : Val S Ψ Γ A) : CtxEq (.app (.ab (C := .arr A C) x a v) u) (.ab x a v) := by
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
  rw [Val.den_wk (A := .res) v η ρ (ℓ, r), hv, Val.den_wk (A := .g .unit) v η' ρ']
  exact TreeRel.abE (d := [Dtor.free ℓ r]) (d' := [Dtor.free ℓ r']) (f := []) (f' := [])
    (W.noPend_both hw _ _ _ _) ((W.sub_both _ _ _ _ _).r' (hη _ x))
    (.cons (.free (W.both_r _ _ _ _ _)) .nil) .nil

/-! ## L2: the handler laws -/

/-- The continuation as a value: a thunk of `resume` (and of a `cancel` that runs nothing, when
the operation may drop it). -/
def kVal {r : G} {C : CTy S} : (b : Bool) → (q : Mode) → Cmp S Ψ (.g r :: Γ) C →
    Val S Ψ Γ (ktyB b q r C)
  | true, _, M => .thunk _ (.rcd (.lam M) (.ret .unit))
  | false, q, M => .thunk q (.lam M)

theorem kVal_den {r : G} {C : CTy S} (b : Bool) (q : Mode) (M : Cmp S Ψ (.g r :: Γ) C)
    (η : IEnv Ψ) (ρ : Env Γ) :
    (kVal b q M).den η ρ = mkK b q r C (fun y => M.den η (ρ.cons y)) (Tree.ret ()) := by
  cases b <;> rfl

/-- **H-ret**: `handle (return v) ≡ h_ret v`. -/
theorem h_ret (e : S.E) (hr : Cmp S Ψ (A :: Γ) C)
    (hop : (o : S.O e) → Cmp S Ψ (kty (S.q e o) (S.res e o) C :: .g (S.arg e o) :: Γ) C)
    (hab : (a : S.A e) → Cmp S Ψ (.g (S.aarg e a) :: Γ) C) (v : Val S Ψ Γ A) :
    CtxEq (.handle e hr hop hab (.ret (v.ren Ren.wk (Ren.id Γ)))) (.bind (.ret v) hr) := by
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
    (hop : (o : S.O e) → Cmp S Ψ (kty (S.q e o) (S.res e o) C :: .g (S.arg e o) :: Γ) C)
    (hab : (a : S.A e) → Cmp S Ψ (.g (S.aarg e a) :: Γ) C) (o : S.O e)
    (v : Val S Ψ Γ (.g (S.arg e o))) (M : Cmp S Ψ (.g (S.res e o) :: Γ) (.F A)) :
    CtxEq (.handleAt x hr hop hab (.op x o v M))
      (.bind (.ret v) (.bind (.ret (kVal (S.q e o).w (S.q e o)
          ((Cmp.handleAt x (hr.ren (Ren.id Ψ) Ren.wk.lift)
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

end EffRel
