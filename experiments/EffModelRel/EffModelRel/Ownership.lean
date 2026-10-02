import EffModelRel.Findings

/-!
# EffModelRel — the ownership fragment: ν under capture, η, hiding (#249 step 1)

**Instance names in a continuation.** In this semantics a name a continuation allocates *after*
its capture point is generated afresh each time it is resumed: `nu` is a node of the tree, run
when the resumption reaches it. A name allocated *before* the capture and still pending (not yet
used) is shared by every resumption. Staton's `ν/op` moves a `ν` across a capture point, from the
first kind to the second.

- **`ν/op` at a linear operation** fails in phase B's contextual equivalence (`nu_op_fails_linear`):
  its contexts are intrinsically typed and ignore modes, so a handler may resume a *linear*
  continuation twice, and phase B's multi-shot counterexample goes through unchanged. So `O1`
  (`docs/effects-tr` T7.15) is a statement about **moded** contexts, `CtxEqM`; it is stated as
  `O1` and not derived here (see below).
- **η, the forwarding handler.** The semantic forwarding handler, whose clause re-performs the
  operation on the same instance *with the destructors it was performed under*, is the identity on
  related trees (`fwd_id`). The syntactic clause `op x.o(p; y. resume k y)` re-performs with no
  destructors, so it loses those of the frames between the operation and the handler:
  - at a linear operation that is observable only at an unhandled operation, where the stack
    unwinds (`eta_fails_linear`), which effect safety excludes for moded programs;
  - at an affine operation it is observable when an outer handler cancels: the resource the
    frame owns leaks (`etaAff_obs`), and the program is not moded (`etaAff_not_moded`): the
    clause's continuation captures `k`, a linear thunk, at an affine operation, which
    independence refuses.
  So η that "forwards cancel, finalisers included" needs a forwarding primitive whose destructor
  is the cancel of `k`; phase B's destructors (`Dtor`: free a resource, write a state back) are
  first order and cannot carry one. `fwd_id` is that primitive's law.
- **Hiding.** A handler's state is invisible to the body: two handlers into state-passing types
  whose clauses simulate each other through a relation on their states relate the handled
  computations at related states (`hnd_sim`), whatever the body. `hiding_counter` instantiates it:
  a counter kept as `n` and one kept as `-n` cannot be told apart by any body. This is the
  relational statement of BoLo's anti-frame for a handler's witness.
-/

namespace EffRel

variable {S : Sig}

/-! ## `ν/op` at a linear operation, in phase B's equivalence -/

/-- `twoClosures` under an outer instance of any effect. -/
def twoClosuresAt {e : Eff} {Γ : List (VTy σ)} : M [.log, e] Γ (.F (.prod predT appT)) :=
  .ret (.pair (.thunk Mode.unr (.ilam (.ieq (.s .z) .z)))
    (.thunk Mode.unr (.lam (.iapp (.force v0) .z))))

def nuOpLinL : M [.log] [] (.F (.prod predT appT)) :=
  .nu .log (.op (.s .z) Op.log (.int 0) twoClosuresAt)

def nuOpLinR : M [.log] [] (.F (.prod predT appT)) :=
  .op .z Op.log (.int 0) (.nu .log twoClosuresAt)

/-- A clause that resumes a linear continuation twice: not moded, but a context of `CtxEq`. -/
def twiceOps {Ψ : List Eff} {Γ : List (VTy σ)} : (o : Op .log) →
    M Ψ (kty (σ.q .log o) Rw.nil (σ.res .log o) (.F (.prod predT appT)) :: .g (σ.arg .log o) :: Γ)
      (.F (.prod predT appT))
  | .log =>
      .bind (.app (.force v0) .unit)
        (.bind (.app (.force v1) .unit)
          (.split v1 (.split v2 (.ret (.pair (.var (.s (.s (.s .z)))) v0)))))

def nuOpLinCtx : Context σ [.log] [] (.F (.prod predT appT)) .bool :=
  .bind (.handle .log Rw.nil (.ret v0) twiceOps (fun a => nomatch a) (.iapp (.force v0) .z))
    (.split v0 (.app (.force v0) v1))

theorem nuOpLin_obs : nuOpLinCtx.obs nuOpLinL.den = ⟨.ret (.bool true), []⟩ ∧
    nuOpLinCtx.obs nuOpLinR.den = ⟨.ret (.bool false), []⟩ := by decide

/-- `ν/op` fails at a **linear** operation in phase B's `CtxEq`: its contexts may resume a linear
continuation twice. -/
theorem nu_op_fails_linear : ¬ CtxEq nuOpLinL nuOpLinR := fun h => by
  have := h .bool nuOpLinCtx
  rw [nuOpLin_obs.1, nuOpLin_obs.2] at this
  cases this

/-! ## Moded contextual equivalence and the statement of O1 -/

/-- Contextual equivalence over **moded** contexts: closing contexts the moded judgement accepts.
The hole is an unrestricted thunk, used through its instances and arguments. -/
def CtxEqM (M N : Cmp S Ψ Γ C) : Prop :=
  ∀ (g : G) (P : Context S Ψ Γ C g) (R : Row S []),
    CM (Ψ := []) VSet.none R P → P.obs M.den = P.obs N.den

theorem CtxEq.toM {M N : Cmp S Ψ Γ C} (h : CtxEq M N) : CtxEqM M N := fun g P _ _ => h g P

/-- **O1** (`docs/effects-tr` T7.15.2): `ν x. op a.o(v; y. M) ≡ op a.o(v; y. ν x. M)` over moded
contexts, at an operation whose qualifier admits no contraction. Not derived: the binary relation
relates an operation only at a world with nothing pending (`TreeRel.op`), so the left's pending
`x` must be read as garbage, and a garbage name is never matched with the right's later one. A
proof needs a relation in which a continuation value owns the pending names it will match, and
whose fundamental property is for moded terms only. The obstruction is not verified to be real. -/
def O1 : Prop :=
  ∀ (Ψ : List S.E) (Γ : List (VTy S)) (C : CTy S) (e e' : S.E) (a : Var Ψ e') (o : S.O e')
    (v : Val S Ψ Γ (.g (S.arg e' o))) (M : Cmp S (e :: Ψ) (.g (S.res e' o) :: Γ) C),
    (S.q e' o).c = false →
    CtxEqM (.nu e (.op (.s a) o (v.ren Ren.wk (Ren.id Γ)) M)) (.op a o v (.nu e M))

/-! ## η: the forwarding handler -/

/-- The forwarding handler's clauses, semantically: return, re-perform with the destructors the
operation was performed under, abort. -/
def fwdRet {A : VTy S} : A.den → (CTy.F A).den := fun x => Tree.ret x
def fwdOp {A : VTy S} (i : Nat) (e : S.E) :
    (o : S.O e) → (S.arg e o).den → ((S.res e o).den → (CTy.F A).den) → List Dtor → (CTy.F A).den :=
  fun o v k d => Tree.op i e o v k d
def fwdAb {A : VTy S} (i : Nat) (e : S.E) : (a : S.A e) → (S.aarg e a).den → (CTy.F A).den :=
  fun a v => Tree.ab i e a v []

/-- **η, semantically.** A handler of `i` whose clauses re-perform each operation on `i` with the
destructors it was performed under, and abort on `i`, is the identity on related trees. -/
theorem fwd_id {A : VTy S} {R : W → A.den → A.den → Prop} {w : W} {t t' : Tree S A.den}
    (h : TreeRel R w t t') (i : Nat) (e : S.E) :
    TreeRel R w t (t'.hnd (.F A) i e fwdRet (fwdOp i e) (fwdAb i e)) := by
  induction h with
  | ret hp hx => exact .ret hp hx
  | @op w j j' e' o v k k' d d' hp hj hd _ ih =>
      simp only [Tree.hnd]
      by_cases hji : j' = i
      · rw [if_pos hji]
        by_cases he : e' = e
        · subst he; subst hji; rw [catchOp_self]; exact .op hp hj hd ih
        · rw [catchOp_ne he]; exact .op hp hj hd ih
      · rw [if_neg hji]; exact .op hp hj hd ih
  | @ab w j j' e' a v d d' hp hj hd =>
      simp only [Tree.hnd]
      by_cases hji : j' = i
      · rw [if_pos hji]
        by_cases he : e' = e
        · subst he; subst hji; rw [catchAb_self, dtorsA_F]
          have := TreeRel.abE (R := R) (f := []) (f' := []) hp hj hd .nil (a := a) (v := v)
          rwa [List.append_nil] at this
        · rw [catchAb_ne he]; exact .ab hp hj hd
      · rw [if_neg hji]; exact .ab hp hj hd
  | @abE w j j' e' a v d d' f f' hp hj hd hf =>
      rw [hnd_dtors, dtorsA_F]
      simp only [Tree.hnd]
      by_cases hji : j' = i
      · rw [if_pos hji]
        by_cases he : e' = e
        · subst he; subst hji; rw [catchAb_self, dtorsA_F]
          show TreeRel R w (Tree.ab j e' a v (d ++ f))
            (Tree.dtors d' (Tree.dtors f' (Tree.ab j' e' a v [])))
          rw [← Tree.dtors_append]
          have := TreeRel.abE (R := R) (f := []) (f' := []) hp hj (hd.append hf) .nil
            (a := a) (v := v)
          rwa [List.append_nil] at this
        · rw [catchAb_ne he]; exact .abE hp hj hd hf
      · rw [if_neg hji]; exact .abE hp hj hd hf
  | act ha _ ih => exact .act ha ih
  | nu _ ih => exact .nu ih
  | nuL _ ih => exact .nuL ih
  | nuR _ ih => exact .nuR ih
  | gL _ ih => exact .gL ih
  | gR _ ih => exact .gR ih
  | mL hi' _ ih => exact .mL hi' ih
  | mR hi _ ih => exact .mR hi ih

/-- The syntactic forwarding clause: `op x.o(p; y. resume k y)`, at `Log`. -/
def fwdLogOps {Ψ : List Eff} {Γ : List (VTy σ)} {C : CTy σ} (x : Var Ψ .log) : (o : Op .log) →
    M Ψ (kty (σ.q .log o) Rw.nil (σ.res .log o) C :: .g (σ.arg .log o) :: Γ) C
  | .log => .op x Op.log v1 (.app (.force v1) v0)

/-- `using r = acquire 1 in log 7` under a forwarding handler of the same instance. -/
def etaLinL : M [.log] [] (.F tInt) :=
  .handleAt .z Rw.nil (.ret v0) (fwdLogOps .z) (fun a => nomatch a)
    (.using 1 (.op (.s .z) Op.log (.int 7) (.ret (.int 0))))

def etaLinR : M [.log] [] (.F tInt) :=
  .using 1 (.op (.s .z) Op.log (.int 7) (.ret (.int 0)))

/-- The hole's instance, unhandled: the stack unwinds. -/
def etaCtx : Context σ [.log] [] (.F tInt) .int :=
  .nu .log (.iapp (.force v0) .z)

theorem eta_obs : etaCtx.obs etaLinL.den = ⟨.unhandled, [.acq 1]⟩ ∧
    etaCtx.obs etaLinR.den = ⟨.unhandled, [.acq 1, .free 1]⟩ := by decide

/-- **η fails in phase B's equivalence at a linear operation**: the forwarded operation carries
no destructors, and an unhandled operation unwinds the stack. -/
theorem eta_fails_linear : ¬ CtxEq etaLinL etaLinR := fun h => by
  have := h .int etaCtx
  rw [eta_obs.1, eta_obs.2] at this
  cases this

/-- A handler of `Yield` that cancels the continuation and answers `0`. -/
def cancelOps {Ψ : List Eff} {Γ : List (VTy σ)} : (o : Op .yld) →
    M Ψ (kty (σ.q .yld o) Rw.nil (σ.res .yld o) (.F tInt) :: .g (σ.arg .yld o) :: Γ) (.F tInt)
  | .yield => .bind (.prj2 (.force v0)) (.ret (.int 0))

/-- The syntactic forwarding clause at `Yield`, which is affine. -/
def fwdYldOps {Ψ : List Eff} {Γ : List (VTy σ)} {C : CTy σ} (x : Var Ψ .yld) : (o : Op .yld) →
    M Ψ (kty (σ.q .yld o) Rw.nil (σ.res .yld o) C :: .g (σ.arg .yld o) :: Γ) C
  | .yield => .op x Op.yield v1 (.app (.prj1 (.force v1)) v0)

/-- An outer handler that cancels, a forwarding handler, and a resource held across the yield. -/
def etaAff : Prog σ .int :=
  .handle .yld Rw.nil (.ret v0) cancelOps (fun a => nomatch a)
    (.handleAt .z Rw.nil (.ret v0) (fwdYldOps .z) (fun a => nomatch a)
      (.using 1 (.op (.s .z) Op.yield (.int 1) (.ret (.int 0)))))

/-- The same without the forwarding handler. -/
def etaAffR : Prog σ .int :=
  .handle .yld Rw.nil (.ret v0) cancelOps (fun a => nomatch a)
    (.using 1 (.op (.s .z) Op.yield (.int 1) (.ret (.int 0))))

theorem etaAff_obs : etaAff.obs = ⟨.ret (.int 0), [.acq 1]⟩ ∧
    etaAffR.obs = ⟨.ret (.int 0), [.acq 1, .free 1]⟩ := by decide

/-- The ghost run, as a function: the answer and the tokens live at the end. -/
def Tree.gRun : Tree S X → SW → Option (X × Own)
  | .ret x, s => some (x, s.live)
  | .op .., _ => none
  | .ab .., _ => none
  | .nu k, s => (k s.w.next).gRun ⟨{ s.w with next := s.w.next + 1 }, s.live⟩
  | .act a k, s =>
      match a.sexec s with
      | none => none
      | some (y, s') => (k y).gRun s'

theorem Tree.Safe.gRun {P : Own → X → Prop} :
    (t : Tree S X) → ∀ s, t.Safe P s → ∃ x O, t.gRun s = some (x, O) ∧ P O x
  | .ret x, _, h => ⟨x, _, rfl, h⟩
  | .op .., _, h => h.elim
  | .ab .., _, h => h.elim
  | .nu k, s, h => by
      simp only [Tree.Safe] at h; simp only [Tree.gRun]
      exact Tree.Safe.gRun (k s.w.next) _ h
  | .act a k, s, h => by
      simp only [Tree.Safe] at h
      simp only [Tree.gRun]
      split at h
      · exact h.elim
      · rename_i y s' hs; rw [hs]; exact Tree.Safe.gRun (k y) s' h

/-- The resource the frame acquired is still live when `etaAff` returns. -/
theorem etaAff_leaks : ((etaAff.den IEnv.nil Env.nil).gRun ⟨Wd.init, 0⟩).map
    (fun p => p.2 .res 1) = some 1 := by decide

/-- The forwarding clause at an affine operation leaks the resource when the outer handler
cancels, so the program is not moded. -/
theorem etaAff_not_moded : ¬ ∃ R, CM (Ψ := []) (Γ := []) VSet.none R etaAff := fun ⟨_, hP⟩ => by
  obtain ⟨x, O, hr, hO⟩ := Tree.Safe.gRun _ _ (safety etaAff hP)
  have h := etaAff_leaks
  rw [hr, hO] at h
  cases h

/-! ## Hiding: the handler's state is invisible to the body -/

/-- **Hiding, as parametricity.** Two handlers into state-passing types, with possibly different
state types, whose clauses map `Rs`-related states to related computations given related
continuations, relate the two handled trees at related states, for any related bodies. -/
theorem hnd_sim {A A' : VTy S} {b b' : Rw} {D : CTy S} {R : W → X → X → Prop}
    {w : W} {t t' : Tree S X} (h : TreeRel R w t t') {i i' : Nat} {e : S.E}
    {hr : X → (CTy.arr A b D).den} {hr' : X → (CTy.arr A' b' D).den}
    {hop : (o : S.O e) → (S.arg e o).den → ((S.res e o).den → (CTy.arr A b D).den) → List Dtor →
      (CTy.arr A b D).den}
    {hop' : (o : S.O e) → (S.arg e o).den → ((S.res e o).den → (CTy.arr A' b' D).den) → List Dtor →
      (CTy.arr A' b' D).den}
    {hab : (a : S.A e) → (S.aarg e a).den → (CTy.arr A b D).den}
    {hab' : (a : S.A e) → (S.aarg e a).den → (CTy.arr A' b' D).den}
    (Rs : A.den → A'.den → Prop) (hi : w.r i i')
    (hR : ∀ w', w.sub w' → w'.noPend → ∀ x x', R w' x x' → ∀ s s', Rs s s' →
      CRU D w' (hr x s) (hr' x' s'))
    (hO : ∀ w', w.sub w' → w'.noPend → ∀ o v k k' d d',
      (∀ y w'', w'.le w'' → ∀ s s', Rs s s' → CRU D w'' (k y s) (k' y s')) → DR w' d d' →
      ∀ s s', Rs s s' → CRU D w' (hop o v k d s) (hop' o v k' d' s'))
    (hA : ∀ w', w.sub w' → w'.noPend → ∀ a v s s', Rs s s' → CRU D w' (hab a v s) (hab' a v s')) :
    ∀ s s', Rs s s' →
      CRU D w ((t.hnd (.arr A b D) i e hr hop hab) s) ((t'.hnd (.arr A' b' D) i' e hr' hop' hab') s') := by
  revert hi hR hO hA
  induction h with
  | ret hp hx => intro _ hR _ _ s s' hs; exact hR _ (W.sub.refl _) hp _ _ hx s s' hs
  | @op w j j' e' o v k k' d d' hp hj hd _ ih =>
      intro hi hR hO hA s s' hs
      have kk : ∀ y s s', Rs s s' → CRU D w ((k y).hnd (.arr A b D) i e hr hop hab s)
          ((k' y).hnd (.arr A' b' D) i' e hr' hop' hab' s') := fun y => ih y hi hR hO hA
      simp only [Tree.hnd]
      by_cases hji : j = i
      · have hji' : j' = i' := (w.r_iff hi hj).1 hji
        rw [if_pos hji, if_pos hji']
        by_cases he : e' = e
        · subst he
          rw [catchOp_self, catchOp_self]
          exact hO _ (W.sub.refl _) hp o v _ _ d d'
            (fun y w'' hle s₁ s₁' hs₁ => CRU.mono D hle (kk y s₁ s₁' hs₁)) hd s s' hs
        · rw [catchOp_ne he, catchOp_ne he]
          exact opA_rel D hp hj hd (fun y => kk y s s' hs)
      · have hji' : ¬ j' = i' := fun h' => hji ((w.r_iff hi hj).2 h')
        rw [if_neg hji, if_neg hji']
        exact opA_rel D hp hj hd (fun y => kk y s s' hs)
  | @ab w j j' e' a v d d' hp hj hd =>
      intro hi _ _ hA s s' hs
      simp only [Tree.hnd]
      by_cases hji : j = i
      · have hji' : j' = i' := (w.r_iff hi hj).1 hji
        rw [if_pos hji, if_pos hji']
        by_cases he : e' = e
        · subst he
          rw [catchAb_self, catchAb_self, dtorsA_arr, dtorsA_arr]
          exact dtorsA_rel D hd (hA _ (W.sub.refl _) hp a v s s' hs)
        · rw [catchAb_ne he, catchAb_ne he]; exact abA_rel D hp hj hd
      · have hji' : ¬ j' = i' := fun h' => hji ((w.r_iff hi hj).2 h')
        rw [if_neg hji, if_neg hji']
        exact abA_rel D hp hj hd
  | @abE w j j' e' a v d d' f f' hp hj hd hf =>
      intro hi _ _ hA s s' hs
      rw [hnd_dtors, dtorsA_arr]
      simp only [Tree.hnd]
      by_cases hji : j = i
      · have hji' : j' = i' := (w.r_iff hi hj).1 hji
        rw [if_pos hji, if_pos hji']
        by_cases he : e' = e
        · subst he
          rw [catchAb_self, catchAb_self, dtorsA_arr, dtorsA_arr]
          simp only [dtorsA_append]
          exact dtorsA_rel D hd (dtorsA_rel D hf (hA _ (W.sub.refl _) hp a v s s' hs))
        · rw [catchAb_ne he, catchAb_ne he]; exact abA_dtors_rel D hp hj hd hf
      · have hji' : ¬ j' = i' := fun h' => hji ((w.r_iff hi hj).2 h')
        rw [if_neg hji, if_neg hji']
        exact abA_dtors_rel D hp hj hd hf
  | act ha _ ih =>
      intro hi hR hO hA s s' hs; exact actA_rel D ha (fun y => ih y hi hR hO hA s s' hs)
  | nu _ ih =>
      intro hi hR hO hA s s' hs
      have hs' := W.sub_both
      exact nuA_both D (fun j j' hj hj' => ih j j' hj hj' ((hs' _ _ _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs' _ _ _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs' _ _ _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs' _ _ _ _ _) h1)) s s' hs)
  | nuL _ ih =>
      intro hi hR hO hA s s' hs
      have hs' := W.sub_pendL
      exact nuA_L D (fun j hj => ih j hj ((hs' _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs' _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs' _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs' _ _ _) h1)) s s' hs)
  | nuR _ ih =>
      intro hi hR hO hA s s' hs
      have hs' := W.sub_pendR
      exact nuA_R D (fun j hj => ih j hj ((hs' _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs' _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs' _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs' _ _ _) h1)) s s' hs)
  | gL _ ih =>
      intro hi hR hO hA s s' hs
      have hs' := W.sub_garbL
      exact nuA_gL D (fun j hj => ih j hj ((hs' _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs' _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs' _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs' _ _ _) h1)) s s' hs)
  | gR _ ih =>
      intro hi hR hO hA s s' hs
      have hs' := W.sub_garbR
      exact nuA_gR D (fun j hj => ih j hj ((hs' _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs' _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs' _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs' _ _ _) h1)) s s' hs)
  | mL hi' _ ih =>
      intro hi hR hO hA s s' hs
      have hs' := W.sub_matchL
      exact nuA_mL D hi' (fun j hj => ih j hj ((hs' _ _ _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs' _ _ _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs' _ _ _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs' _ _ _ _ _) h1)) s s' hs)
  | mR hi₀ _ ih =>
      intro hi hR hO hA s s' hs
      have hs' := W.sub_matchR
      exact nuA_mR D hi₀ (fun j hj => ih j hj ((hs' _ _ _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs' _ _ _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs' _ _ _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs' _ _ _ _ _) h1)) s s' hs)

end EffRel

/-! ## Hiding, an instance: a counter kept as `n` or as `-n` -/

namespace EffRel

section Counter

variable {Ψ : List Eff} {Γ : List (VTy σ)} {B : VTy σ}

abbrev cTy (B : VTy σ) : CTy σ := .arr tInt Rw.nil (.F B)

/-- Return the body's answer; drop the state. -/
def cRet : M Ψ (B :: Γ) (cTy B) := .lam (.ret v1)

/-- The counter as `n`: `inc` adds one, `get` answers the state. -/
def cOpsUp : (o : Op .ctr) →
    M Ψ (kty (σ.q .ctr o) Rw.nil (σ.res .ctr o) (cTy B) :: .g (σ.arg .ctr o) :: Γ) (cTy B)
  | .inc => .lam (.bind (.prim .add v0 (.int 1)) (.app (.app (.force v2) .unit) v0))
  | .get => .lam (.app (.app (.force v1) v0) v0)

/-- The counter as `-n`: `inc` subtracts one, `get` answers the negated state. -/
def cOpsDown : (o : Op .ctr) →
    M Ψ (kty (σ.q .ctr o) Rw.nil (σ.res .ctr o) (cTy B) :: .g (σ.arg .ctr o) :: Γ) (cTy B)
  | .inc => .lam (.bind (.prim .sub v0 (.int 1)) (.app (.app (.force v2) .unit) v0))
  | .get => .lam (.bind (.prim .sub (.int 0) v0) (.app (.app (.force v2) v0) v1))

/-- **Hiding.** No body tells a counter kept as `n` from one kept as `-n`. -/
theorem hiding_counter (N : M (.ctr :: Ψ) Γ (.F B)) :
    CtxEq (S := σ) (.app (.handle Eff.ctr Rw.nil cRet cOpsUp (fun a => nomatch a) N) (.int 0))
      (.app (.handle Eff.ctr Rw.nil cRet cOpsDown (fun a => nomatch a) N) (.int 0)) := by
  apply soundness
  intro w hw η η' ρ ρ' hη hρ
  simp only [Cmp.den, CTy.nuA]
  apply nuA_both
  intro i i' hi hi'
  have hs := W.sub_both w i i' hi hi'
  refine hnd_sim (CRU_F.1 (Cmp.fp N (W.noPend_both hw _ _ _ _)
      (IR.cons (hη.sub hs) (W.both_r _ _ _ _ _) _) (hρ.mono hs)))
    (A := tInt) (A' := tInt) (Rs := fun (s s' : Int) => s' = -s) (W.both_r _ _ _ _ _) ?_ ?_ ?_
    _ _ (by simp [Val.den])
  · intro w' _ hp x x' hx s s' _
    exact CRU_F.2 (.ret hp hx)
  · intro w' _ hp o v k k' d d' hk _ (s : Int) (s' : Int) hss
    subst hss
    cases o with
    | inc =>
        show CRU (CTy.F B) w' (k () (s + 1)) (k' () (-s - 1))
        exact hk () w' (W.le.refl _) _ _ (show -s - 1 = -(s + 1) by omega)
    | get =>
        show CRU (CTy.F B) w' (k s s) (k' ((0 : Int) - -s) (-s))
        have h0 : (0 : Int) - -s = s := by omega
        rw [h0]
        exact hk s w' (W.le.refl _) _ _ rfl
  · intro _ _ _ a; exact nomatch a

end Counter

end EffRel
