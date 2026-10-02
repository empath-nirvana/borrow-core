import EffModelRel.Laws

/-!
# EffModelRel — the tensor: operations on disjoint capabilities commute

Two capabilities lent to one computation are run by two comodels with separate cells. When the
co-operations answer in place (they perform nothing and never fail), operations on the two
instances commute: running is the tensor of the two comodels with the computation.
-/

namespace EffRel

variable {S : Sig}

/-- A ground literal. -/
def Val.lit : (g : G) → g.den → Val S Ψ Γ (.g g)
  | .unit, _ => .unit
  | .int, n => .int n
  | .bool, b => .bool b
  | .void, x => (x : Empty).elim

theorem Val.lit_den (g : G) (x : g.den) (η : IEnv (S := S) Ψ) (ρ : Env Γ) :
    (Val.lit g x).den η ρ = x := by
  cases g <;> first | rfl | exact (x : Empty).elim

/-- Co-operations that answer in place: no effect, no error. -/
def PureCo {e : S.E} {s : G}
    (co : (o : S.O e) → Cmp S [] [.g s, .g (S.arg e o)] (.F (coRes S e s o))) : Prop :=
  ∀ o a st, ∃ r st', (co o).den IEnv.nil ((Env.nil.cons (VTy.gv a)).cons (VTy.gv st)) =
    Tree.ret (.inl (r, st'))

/-- Two runners, one inside the other, each answering one operation of the client in turn. -/
theorem runL_pair {X : Type} {e₁ e₂ : S.E} {s₁ s₂ : G} {co₁ : CoSem S e₁ s₁} {co₂ : CoSem S e₂ s₂}
    {x₁ x₂ c₁ c₂ : Nat} (hx : x₁ ≠ x₂) (o₁ : S.O e₁) (o₂ : S.O e₂) (v₁ v₂)
    {st₁ st₁' : s₁.den} {st₂ st₂' : s₂.den} {r₁ r₂}
    (h₁ : co₁ o₁ v₁ st₁ = Tree.ret (.inl (r₁, st₁')))
    (h₂ : co₂ o₂ v₂ st₂ = Tree.ret (.inl (r₂, st₂')))
    (k : (S.res e₁ o₁).den → (S.res e₂ o₂).den → Tree S X) :
    ((Tree.op x₁ e₁ o₁ v₁ (fun y₁ => Tree.op x₂ e₂ o₂ v₂ (fun y₂ => k y₁ y₂) []) []).runL
        x₂ e₂ c₂ s₂ co₂ st₂).runL x₁ e₁ c₁ s₁ co₁ st₁ =
      ((k r₁ r₂).runL x₂ e₂ c₂ s₂ co₂ st₂').runL x₁ e₁ c₁ s₁ co₁ st₁' := by
  simp only [Tree.runL, if_neg hx, ↓reduceIte, coStep_self, h₁, h₂, Tree.bind, coK]

theorem runL_pair' {X : Type} {e₁ e₂ : S.E} {s₁ s₂ : G} {co₁ : CoSem S e₁ s₁}
    {co₂ : CoSem S e₂ s₂} {x₁ x₂ c₁ c₂ : Nat} (hx : x₁ ≠ x₂) (o₁ : S.O e₁) (o₂ : S.O e₂) (v₁ v₂)
    {st₁ st₁' : s₁.den} {st₂ st₂' : s₂.den} {r₁ r₂}
    (h₁ : co₁ o₁ v₁ st₁ = Tree.ret (.inl (r₁, st₁')))
    (h₂ : co₂ o₂ v₂ st₂ = Tree.ret (.inl (r₂, st₂')))
    (k : (S.res e₂ o₂).den → (S.res e₁ o₁).den → Tree S X) :
    ((Tree.op x₂ e₂ o₂ v₂ (fun y₂ => Tree.op x₁ e₁ o₁ v₁ (fun y₁ => k y₂ y₁) []) []).runL
        x₂ e₂ c₂ s₂ co₂ st₂).runL x₁ e₁ c₁ s₁ co₁ st₁ =
      ((k r₂ r₁).runL x₂ e₂ c₂ s₂ co₂ st₂').runL x₁ e₁ c₁ s₁ co₁ st₁' := by
  simp only [Tree.runL, if_neg hx, ↓reduceIte, coStep_self, h₁, h₂, Tree.bind, coK,
    if_neg (Ne.symm hx)]


/-- The semantics of a capability's closed co-operations. -/
def coSem {e : S.E} {s : G}
    (co : (o : S.O e) → Cmp S [] [.g s, .g (S.arg e o)] (.F (coRes S e s o))) : CoSem S e s :=
  fun o a st => (co o).den IEnv.nil ((Env.nil.cons (VTy.gv a)).cons (VTy.gv st))

/-- A capability over matched cells, with the same closed co-operations, is related to itself. -/
theorem cap_rel {e : S.E} {s : G}
    (co : (o : S.O e) → Cmp S [] [.g s, .g (S.arg e o)] (.F (coRes S e s o)))
    {w : W} {c c' : Nat} (hc : w.r c c') :
    VR (.cap e s) w (VTy.capv c (coSem co)) (VTy.capv c' (coSem co)) := by
  refine VR_cap.2 ⟨hc, fun w' hle o a st => ?_⟩
  have hp' : w'.noPend := hle.noPend' (W.gcP_noPend _)
  exact (CRU_F.1 (Cmp.fp (co o) hp' (IR.nil _)
    (ER.cons (ER.cons (ER.nil _) (VR_g.2 rfl)) (VR_g.2 rfl)))).mapR (fun _ _ _ h => VR_coRes h)

theorem W.both_ne {w : W} {i i' : Nat} {hi hi'} {j : Nat}
    (hj : (w.both i i' hi hi').sl j = .free) : j ≠ i := by
  intro h; subst h; simp [W.both, W.link, upd] at hj

theorem W.both_neR {w : W} {i i' : Nat} {hi hi'} {j : Nat}
    (hj : (w.both i i' hi hi').sr j = .free) : j ≠ i' := by
  intro h; subst h; simp [W.both, W.link, upd] at hj

/-- Closed co-operations are related to themselves at every world. -/
theorem coSem_rel {e : S.E} {s : G}
    (co : (o : S.O e) → Cmp S [] [.g s, .g (S.arg e o)] (.F (coRes S e s o))) {w : W}
    (hw : w.noPend) (o : S.O e) (a) (st) :
    TreeRel (fun _ x x' => x = x') w (coSem co o a st) (coSem co o a st) :=
  (CRU_F.1 (Cmp.fp (co o) hw (IR.nil _)
    (ER.cons (ER.cons (ER.nil _) (VR_g.2 rfl)) (VR_g.2 rfl)))).mapR (fun _ _ _ h => VR_coRes h)

/-- **Tensor**: on two capabilities with co-operations that answer in place, operations
commute: `op_x₁ v₁; op_x₂ v₂; K ≡ op_x₂ v₂; op_x₁ v₁; K`. -/
theorem tensor {e₁ e₂ : S.E} {s₁ s₂ : G}
    (co₁ : (o : S.O e₁) → Cmp S [] [.g s₁, .g (S.arg e₁ o)] (.F (coRes S e₁ s₁ o)))
    (co₂ : (o : S.O e₂) → Cmp S [] [.g s₂, .g (S.arg e₂ o)] (.F (coRes S e₂ s₂ o)))
    (h₁ : PureCo co₁) (h₂ : PureCo co₂) (a₁ : Val S Ψ Γ (.g s₁)) (a₂ : Val S Ψ Γ (.g s₂))
    (o₁ : S.O e₁) (o₂ : S.O e₂) (v₁ : (S.arg e₁ o₁).den) (v₂ : (S.arg e₂ o₂).den)
    (K : Cmp S (e₂ :: e₁ :: Ψ)
      (.g (S.res e₂ o₂) :: .g (S.res e₁ o₁) :: .cap e₂ s₂ :: .cap e₁ s₁ :: Γ) (.F A)) :
    CtxEq
      (.bind (.newcap e₁ s₁ co₁ a₁) (.bind (.newcap e₂ s₂ co₂ a₂.wk)
        (.lend (.var (.s .z)) (.lend (.var .z)
          (.op (.s .z) o₁ (.lit _ v₁) (.op .z o₂ (.lit _ v₂) K))))))
      (.bind (.newcap e₁ s₁ co₁ a₁) (.bind (.newcap e₂ s₂ co₂ a₂.wk)
        (.lend (.var (.s .z)) (.lend (.var .z)
          (.op .z o₂ (.lit _ v₂) (.op (.s .z) o₁ (.lit _ v₁) (K.ren (Ren.id _) Ren.swap))))))) := by
  apply soundness
  intro w hw η η' ρ ρ' hη hρ
  have ha₁ := VR_g.1 (Val.fp a₁ hw hη hρ)
  have ha₂ := VR_g.1 (Val.fp a₂ hw hη hρ)
  simp only [Cmp.den, Tree.bindC, CTy.nuA, CTy.actA, Val.den, Env.cons, IEnv.cons]
  apply CRU_F.2
  refine .nu (fun c₁ c₁' hc₁ hc₁' => ?_)
  have e1 : (⟨s₁, a₁.den η ρ⟩ : GVal) = ⟨s₁, a₁.den η' ρ'⟩ := by rw [ha₁]
  rw [e1]
  refine .act (.new (W.both_r _ _ _ _ _)) (fun _ => .nu (fun c₂ c₂' hc₂ hc₂' => ?_))
  have e2 : (⟨s₂, a₂.wk.den η (ρ.cons (VTy.capv c₁ (coSem co₁)))⟩ : GVal) =
      ⟨s₂, a₂.wk.den η' (ρ'.cons (VTy.capv c₁' (coSem co₁)))⟩ :=
    congrArg (Sigma.mk s₂) ((Val.den_wk a₂ η ρ _).trans (ha₂.trans (Val.den_wk a₂ η' ρ' _).symm))
  refine TreeRel.of_eq (congrArg (fun z => Tree.act (Act.new c₂ z) _) e2) ?_
  refine .act (.new (W.both_r _ _ _ _ _)) (fun _ => ?_)
  have hc₁w := (W.sub_both _ c₂ c₂' hc₂ hc₂').r' (W.both_r w c₁ c₁' hc₁ hc₁')
  refine .act (.rd hc₁w) (fun st₁ => .nu (fun x₁ x₁' hx₁ hx₁' => ?_))
  refine .act (.rd ((W.sub_both _ x₁ x₁' hx₁ hx₁').r' (W.both_r _ c₂ c₂' hc₂ hc₂')))
    (fun st₂ => .nu (fun x₂ x₂' hx₂ hx₂' => ?_))
  have hx : x₁ ≠ x₂ := Ne.symm (W.both_ne hx₂)
  have hx' : x₁' ≠ x₂' := Ne.symm (W.both_neR hx₂')
  simp only [Val.lit_den]
  obtain ⟨r₁, t₁, hco₁⟩ := h₁ o₁ v₁ st₁
  obtain ⟨r₂, t₂, hco₂⟩ := h₂ o₂ v₂ st₂
  refine TreeRel.of_eq (runL_pair (co₁ := coSem co₁) (co₂ := coSem co₂) hx o₁ o₂ v₁ v₂ hco₁ hco₂ _) ?_
  refine TreeRel.of_eq' (runL_pair' (co₁ := coSem co₁) (co₂ := coSem co₂) hx' o₁ o₂ v₁ v₂ hco₁ hco₂ _) ?_
  have hw₁ := W.noPend_both hw c₁ c₁' hc₁ hc₁'
  have hw₂ := W.noPend_both hw₁ c₂ c₂' hc₂ hc₂'
  have hw₃ := W.noPend_both hw₂ x₁ x₁' hx₁ hx₁'
  have hw₄ := W.noPend_both hw₃ x₂ x₂' hx₂ hx₂'
  have s₁ := W.sub_both w c₁ c₁' hc₁ hc₁'
  have s₂ := W.sub_both _ c₂ c₂' hc₂ hc₂'
  have s₃ := W.sub_both _ x₁ x₁' hx₁ hx₁'
  have s₄ := W.sub_both _ x₂ x₂' hx₂ hx₂'
  have s₂₄ := s₂.trans (s₃.trans s₄)
  have s₃₄ := s₃.trans s₄
  have s₁₄ := s₁.trans s₂₄
  refine runL_rel (R := fun w a a' => VR (.sum A (.g .int)) w a a')
    (R2 := fun w a a' => VR (.sum (.sum A (.g .int)) (.g .int)) w a a')
    (fun _ _ _ _ h1 h2 => VR.mono _ h1.sub h2) (fun _ _ _ h => VR_inl.2 h)
    (fun _ _ => VR_inr.2 (VR_g.2 rfl)) ?_ (s₄.r' (W.both_r _ x₁ x₁' hx₁ hx₁'))
    (s₂₄.r' (W.both_r w c₁ c₁' hc₁ hc₁')) (fun w' _ hp o a st => coSem_rel co₁ hp o a st) t₁
  refine runL_rel (R := fun w a a' => VR A w a a')
    (R2 := fun w a a' => VR (.sum A (.g .int)) w a a')
    (fun _ _ _ _ h1 h2 => VR.mono _ h1.sub h2) (fun _ _ _ h => VR_inl.2 h)
    (fun _ _ => VR_inr.2 (VR_g.2 rfl)) ?_ (W.both_r _ x₂ x₂' hx₂ hx₂')
    (s₃₄.r' (W.both_r _ c₂ c₂' hc₂ hc₂')) (fun w' _ hp o a st => coSem_rel co₂ hp o a st) t₂
  refine TreeRel.of_eq' (Cmp.den_ren (Ren.id _) Ren.swap K _ _ _
    ((((((ρ'.cons (VTy.capv c₁' (coSem co₁))).cons (VTy.capv c₂' (coSem co₂))).cons
      (VTy.gv r₁)).cons (VTy.gv r₂))))
    (fun _ _ => rfl) (fun B z => by rcases z with _ | _ | z <;> rfl)) ?_
  refine CRU_F.1 (Cmp.fp K hw₄ ?_ ?_)
  · intro e' z
    rcases z with _ | _ | z
    · exact W.both_r _ x₂ x₂' hx₂ hx₂'
    · exact s₄.r' (W.both_r _ x₁ x₁' hx₁ hx₁')
    · exact s₁₄.r' (hη _ z)
  · intro B z
    rcases z with _ | _ | _ | _ | z
    · exact VR_g.2 rfl
    · exact VR_g.2 rfl
    · exact cap_rel co₂ (s₃₄.r' (W.both_r _ c₂ c₂' hc₂ hc₂'))
    · exact cap_rel co₁ (s₂₄.r' (W.both_r w c₁ c₁' hc₁ hc₁'))
    · exact VR.mono _ s₁₄ (hρ _ z)

end EffRel
