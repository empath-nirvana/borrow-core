import LeafPlaces.Terms

/-!
# Typing the struct operations

Each operation's rule is a derived rule of `DerivesWf`, by induction on the shape; no
constructor is added, so the Fundamental Property and adequacy cover every program that uses
them.

    allocS σ   : valTy σ ⊸ refTy σ
    freeS σ    : refTy σ ⊸ valTy σ
    withborS σ : refTy σ ⊸ (∀'c ⊏ ⊓Δ. famTy M 'c σ ⊸ ['c] T) ⊸ refTy σ ⊗ T

`withborS` at a node follows `Places.withbor2_wf`: the outer family is borrowed at `'x ⊏ ⊓Δ`,
the inner one at `'y ⊏ ⊓(Δ, 'x)`, `⇓s₁` shortens the outer family from `'x` to `'y` leaf by leaf
(`⊑Mut`/`⊑Imm`), and the callback is instantiated at `'y`.  The outer callback's result
`refTy s₂ ⊗ T` is boxed at `'x`, which needs `T` to outlive `'x`: here `T` is plain.
-/

noncomputable section

namespace BoCa.LeafPlaces
open BoCa BoCa.Lifetime BoCa.Programs BoCa.Records

/-! ## Fresh lifetime variables -/

theorem assocFind_none_of_gt {β : Type} (x : LifeVar) :
    ∀ l : List (LifeVar × β), (∀ p ∈ l, p.1 < x) → assocFind x l = none
  | [], _ => rfl
  | (k, v) :: t, h => by
      have hk : k ≠ x := Nat.ne_of_lt (h (k, v) (List.mem_cons_self ..))
      simp only [assocFind, hk, if_false]
      exact assocFind_none_of_gt x t fun p hp => h p (List.mem_cons_of_mem _ hp)

theorem exists_fresh_var (Δ : LifeCtx) (c : LifeVar) : ∃ x, Δ.find? x = none ∧ x ≠ c := by
  refine ⟨c + 1 + (Δ.entries.map Prod.fst).sum, assocFind_none_of_gt _ _ fun p hp => ?_, ?_⟩
  · have h₁ : p.1 ≤ (Δ.entries.map Prod.fst).sum := List.le_sum_of_mem (List.mem_map_of_mem hp)
    exact Nat.lt_of_le_of_lt h₁ (Nat.lt_add_of_pos_left (Nat.succ_pos c))
  · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self c) (Nat.le_add_right _ _))

/-! ## Scoping and binders of the callback type -/

/-- `∀'c ⊏ @bnd. famTy M 'c σ ⊸ ['c] T`. -/
def cbT (M : Life → Ty → Ty) (c : LifeVar) (bnd : Life) (σ : Shape) (T : Ty) : Ty :=
  .all c bnd (.lolli (σ.famTy M (.var c)) (.box (.var c) T))

/-- `refTy σ ⊸ cbT ⊸ refTy σ ⊗ T`. -/
def wTy (M : Life → Ty → Ty) (c : LifeVar) (bnd : Life) (σ : Shape) (T : Ty) : Ty :=
  .lolli σ.refTy (.lolli (cbT M c bnd σ T) (.tensor σ.refTy T))

variable {M : Life → Ty → Ty} {side : LifeCtx → Ty → Prop}

theorem cbT_scoped (F : Former M side) {Δ : LifeCtx} {c : LifeVar} {σ : Shape} {T : Ty}
    (hσ : σ.plain = true) (hT : plainB T = true) (hc : Δ.find? c = none) :
    (cbT M c Δ.meetOfDom σ T).scopedB Δ = true := by
  simp [cbT, Ty.scopedB, hc, Places.meetOfDom_wf, Shape.famTy_scoped F (Places.wf_var_self _ _ _) hσ,
    Places.wf_var_self, plain_scoped hT]

theorem cbT_binds (F : Former M side) {c z : LifeVar} {bnd : Life} {σ : Shape} {T : Ty}
    (hσ : σ.plain = true) (hT : plainB T = true) (hz : c ≠ z) :
    (cbT M c bnd σ T).bindsB z = false := by
  simp [cbT, Ty.bindsB, hz, Shape.famTy_binds F hσ, plain_binds hT]

theorem cbT_inst (F : Former M side) {c : LifeVar} {a : Life} {σ : Shape} {T : Ty}
    (hσ : σ.plain = true) (hT : plainB T = true) :
    Ty.instLife c a (.lolli (σ.famTy M (.var c)) (.box (.var c) T))
      = .lolli (σ.famTy M a) (.box a T) := by
  simp [Ty.instLife, Ty.applyLSub, Shape.famTy_lsub F hσ, plain_lsub hT, Life.applySub, assocFind]

/-! ## `allocS` and `freeS` -/

theorem allocS_wf : ∀ {σ : Shape}, σ.plain = true → ∀ {Δ : LifeCtx} {Γ : Ctx Ty}, Ctx.Dead Γ →
    DerivesWf Δ Γ (allocS σ) (.lolli σ.valTy σ.refTy)
  | .leaf _, _, _, _, hΓ => .allocAx hΓ
  | .node s₁ s₂, h, _, _, hΓ => by
      simp only [Shape.plain, Bool.and_eq_true] at h
      refine .lolliI (plain_scoped (Shape.valTy_plain (σ := .node s₁ s₂) (by simp [Shape.plain, h]))) ?_
      refine .tensorE (.left hΓ.split) (plain_scoped (Shape.valTy_plain (σ := .node s₁ s₂)
        (by simp [Shape.plain, h]))) (.var (.here hΓ)) ?_
      refine .tensorI (.right (.left (.dead hΓ.split))) ?_ ?_
      · exact .lolliE (.dead (.left (.dead hΓ.split))) (.var (.there (.here (.cons hΓ))))
          (allocS_wf h.1 (by dead))
      · exact .lolliE (.left (.dead (.dead hΓ.split))) (.var (.here (.cons (.cons hΓ))))
          (allocS_wf h.2 (by dead))

theorem freeS_wf : ∀ {σ : Shape}, σ.plain = true → ∀ {Δ : LifeCtx} {Γ : Ctx Ty}, Ctx.Dead Γ →
    DerivesWf Δ Γ (freeS σ) (.lolli σ.refTy σ.valTy)
  | .leaf _, _, _, _, hΓ => .freeAx hΓ
  | .node s₁ s₂, h, _, _, hΓ => by
      simp only [Shape.plain, Bool.and_eq_true] at h
      refine .lolliI (plain_scoped (Shape.refTy_plain (σ := .node s₁ s₂) (by simp [Shape.plain, h]))) ?_
      refine .tensorE (.left hΓ.split) (plain_scoped (Shape.refTy_plain (σ := .node s₁ s₂)
        (by simp [Shape.plain, h]))) (.var (.here hΓ)) ?_
      refine .tensorI (.right (.left (.dead hΓ.split))) ?_ ?_
      · exact .lolliE (.dead (.left (.dead hΓ.split))) (.var (.there (.here (.cons hΓ))))
          (freeS_wf h.1 (by dead))
      · exact .lolliE (.left (.dead (.dead hΓ.split))) (.var (.here (.cons (.cons hΓ))))
          (freeS_wf h.2 (by dead))

/-! ## `⇓σ`: a family moved to a shorter lifetime -/

theorem shortenE_wf (F : Former M side) : ∀ {σ : Shape}, σ.plain = true →
    ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {a b : Life}, b.wf Δ = true →
    DerivesWf Δ Γ e (σ.famTy M b) → Δ.EntailsLe a b → DerivesWf Δ Γ (shortenE σ e) (σ.famTy M a)
  | .leaf _, _, _, _, _, _, _, _, h, hle => F.bw.sub h hle
  | .node s₁ s₂, hσ, _, Γ, _, _, _, hb, h, hle => by
      simp only [Shape.plain, Bool.and_eq_true] at hσ
      refine .tensorE (split_kill' Γ) (by simp [Ty.scopedB, Shape.famTy_scoped F hb hσ.1,
        Shape.famTy_scoped F hb hσ.2]) h ?_
      exact .tensorI (.right (.left (kill_dead Γ).split))
        (shortenE_wf F hσ.1 hb (.var (.there (.here (kill_dead Γ)))) hle)
        (shortenE_wf F hσ.2 hb (.var (.here (.cons (kill_dead Γ)))) hle)

/-! ## `withborS` -/

theorem nb_cons {x : LifeVar} {Γ : Ctx Ty} {S : Ty} {l : Bool} (h : l = true → S.bindsB x = false)
    (hΓ : ∀ s ∈ Γ, s.live = true → s.ty.bindsB x = false) :
    ∀ s ∈ (⟨S, l⟩ :: Γ : Ctx Ty), s.live = true → s.ty.bindsB x = false := by
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs
  · exact h hl
  · exact hΓ s hs hl

/-- **The derived rule.**  `withborS σ : refTy σ ⊸ (∀'c ⊏ ⊓Δ. famTy M 'c σ ⊸ ['c] T) ⊸ refTy σ ⊗ T`,
at `M = Mut` (`formerMut`) and `M = Imm` (`formerImm`). -/
theorem withborS_wf (F : Former M side) : ∀ {σ : Shape}, σ.plain = true →
    ∀ {Δ : LifeCtx} {Γ : Ctx Ty} (c : LifeVar) {T : Ty}, plainB T = true → Δ.find? c = none →
    Ctx.Dead Γ → DerivesWf Δ Γ (withborS σ) (wTy M c Δ.meetOfDom σ T)
  | .leaf S, hσ, Δ, _, c, T, hT, hc, hΓ => by
      have hS : plainB S = true := by simpa [Shape.plain] using hσ
      refine F.bw.ax (T₂ := T) c hΓ hc (F.side_plain Δ S hS) ?_
      simp [Places.axTy, Ty.scopedB, hc, Places.meetOfDom_wf, F.scopedM, Places.wf_var_self,
        plain_scoped hS, plain_scoped hT]
  | .node s₁ s₂, hσ, Δ, Γ, c, T, hT, hc, hΓ => by
      have hσ' := hσ
      simp only [Shape.plain, Bool.and_eq_true] at hσ'
      obtain ⟨hp₁, hp₂⟩ := hσ'
      obtain ⟨x, hx, hxc⟩ := exists_fresh_var Δ c
      obtain ⟨y, hy, hyc⟩ := exists_fresh_var (Places.D₁ Δ x) c
      have hxy : x ≠ y := by
        intro e; subst e; simp [Places.D₁, LifeCtx.find?_extend] at hy
      have hR₁ := Shape.refTy_plain hp₁
      have hR₂ := Shape.refTy_plain hp₂
      have hR := Shape.refTy_plain hσ
      have hT' : plainB (.tensor s₂.refTy T) = true := by simp [plainB, hR₂, hT]
      have hcx : (Places.D₁ Δ x).find? c = none := by
        simp [Places.D₁, LifeCtx.find?_extend, hxc, hc]
      have hcy : (Places.D₂ Δ x y).find? c = none := by
        simp [Places.D₂, LifeCtx.find?_extend, hyc, hcx]
      have hwfx : (Life.var x).wf (Places.D₁ Δ x) = true := Places.wf_var_self _ _ _
      have hwfx₂ : (Life.var x).wf (Places.D₂ Δ x y) = true := Places.wf_var_extend hwfx
      -- the inner callback, at `Δ, 'x, 'y`
      have hinner : DerivesWf (Places.D₁ Δ x)
          (⟨s₁.famTy M (.var x), true⟩ :: ⟨.unit, false⟩ :: ⟨s₂.refTy, false⟩ ::
            ⟨s₁.refTy, false⟩ :: ⟨cbT M c Δ.meetOfDom (.node s₁ s₂) T, true⟩ ::
            ⟨(Shape.node s₁ s₂).refTy, false⟩ :: Γ)
          (innerS s₁) (cbT M y (Places.D₁ Δ x).meetOfDom s₂ T) := by
        refine .allI (S := .unit) hy (Places.meetOfDom_wf _) ?_ ?_
        · refine nb_cons (fun _ => Shape.famTy_binds F hp₁) (nb_cons (by simp)
            (nb_cons (by simp) (nb_cons (by simp) (nb_cons (fun _ => cbT_binds F hσ hT (Ne.symm hyc))
              (nb_cons (by simp) (Ctx.Dead.noBinds hΓ y))))))
        refine .lolliI (Shape.famTy_scoped F (Places.wf_var_self _ _ _) hp₂) ?_
        have hg := DerivesWf.allE (Δ := Places.D₂ Δ x y) (a := .var y)
          (Γ := ⟨s₂.famTy M (.var y), false⟩ :: ⟨.unit, false⟩ :: ⟨s₁.famTy M (.var x), false⟩ ::
            ⟨.unit, false⟩ :: ⟨s₂.refTy, false⟩ :: ⟨s₁.refTy, false⟩ ::
            ⟨cbT M c Δ.meetOfDom (.node s₁ s₂) T, true⟩ :: ⟨(Shape.node s₁ s₂).refTy, false⟩ :: Γ)
          (.var (.there (.there (.there (.there (.there (.there (.here (.cons hΓ))))))))) 
          (Places.entailsLt_inner Δ x y)
        rw [cbT_inst F hσ hT] at hg
        refine .lolliE (.left (.dead (.left (.dead (.dead (.dead (.right (.dead hΓ.split))))))))
          ?_ hg
        refine .tensorI (.right (.dead (.left (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))
          ?_ (.var (.here (by dead)))
        exact shortenE_wf F hp₁ hwfx₂ (.var (.there (.there (.here (by dead)))))
          (Places.entailsLe_inner Δ x y)
      -- the outer callback, at `Δ, 'x`
      have houter : DerivesWf Δ
          (⟨s₂.refTy, true⟩ :: ⟨s₁.refTy, false⟩ :: ⟨cbT M c Δ.meetOfDom (.node s₁ s₂) T, true⟩ ::
            ⟨(Shape.node s₁ s₂).refTy, false⟩ :: Γ)
          (outerS s₁ s₂) (cbT M x Δ.meetOfDom s₁ (.tensor s₂.refTy T)) := by
        refine .allI (S := .unit) hx (Places.meetOfDom_wf _) ?_ ?_
        · exact nb_cons (fun _ => plain_binds hR₂) (nb_cons (by simp)
            (nb_cons (fun _ => cbT_binds F hσ hT (Ne.symm hxc)) (nb_cons (by simp) (Ctx.Dead.noBinds hΓ x))))
        refine .lolliI (Shape.famTy_scoped F hwfx hp₁) ?_
        refine .tensorE (T₁ := s₂.refTy) (T₂ := T) (.left (.dead (.left (.dead (.left (.dead hΓ.split))))))
          (by simp [Ty.scopedB, plain_scoped hR₂, plain_scoped hT]) ?_ ?_
        · refine .lolliE (.left (.dead (.right (.dead (.left (.dead hΓ.split)))))) hinner ?_
          exact .lolliE (.dead (.dead (.left (.dead (.dead (.dead hΓ.split))))))
            (.var (.there (.there (.here (by dead))))) (withborS_wf F hp₂ y hT hy (by dead))
        · exact .boxIctx (.tensorI (.right (.left (Ctx.Dead.split (by dead))))
              (.var (.there (.here (by dead)))) (.var (.here (by dead))))
            (Places.outlives_two (LifeCtx.defines_of_wf hwfx) (plain_outlives hT)
              (plain_outlives hR₂) (by dead))
      -- the family rule
      refine .lolliI (plain_scoped hR) (.lolliI (cbT_scoped F hσ hT hc) ?_)
      refine .tensorE (.right (.left hΓ.split)) (plain_scoped hR) (.var (.there (.here hΓ))) ?_
      refine .tensorE (T₁ := s₁.refTy) (T₂ := .tensor s₂.refTy T) (.left (.left (.left (.dead hΓ.split))))
        (by simp [Ty.scopedB, plain_scoped hR₁, plain_scoped hR₂, plain_scoped hT]) ?_ ?_
      · refine .lolliE (.left (.right (.left (.dead hΓ.split)))) houter ?_
        exact .lolliE (.dead (.left (.dead (.dead hΓ.split)))) (.var (.there (.here (by dead))))
          (withborS_wf F hp₁ x hT' hx (by dead))
      refine .tensorE (T₁ := s₂.refTy) (T₂ := T) (.left (.right (Ctx.Dead.split (by dead))))
        (by simp [Ty.scopedB, plain_scoped hR₂, plain_scoped hT]) (.var (.here (by dead))) ?_
      exact .tensorI (.right (.left (.dead (.left (Ctx.Dead.split (by dead))))))
        (.tensorI (.dead (.right (.dead (.left (Ctx.Dead.split (by dead))))))
          (.var (.there (.there (.there (.here (by dead)))))) (.var (.there (.here (by dead)))))
        (.var (.here (by dead)))

/-- `withborS` at `Mut`: every leaf mutably borrowed at one lifetime. -/
theorem withborSM_wf {σ : Shape} (hσ : σ.plain = true) {Δ : LifeCtx} {Γ : Ctx Ty} (c : LifeVar)
    {T : Ty} (hT : plainB T = true) (hc : Δ.find? c = none) (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ (withborS σ) (wTy Places.mutM c Δ.meetOfDom σ T) :=
  withborS_wf formerMut hσ c hT hc hΓ

/-- `withborS` at `Imm`: every leaf immutably borrowed at one lifetime. -/
theorem withborSI_wf {σ : Shape} (hσ : σ.plain = true) {Δ : LifeCtx} {Γ : Ctx Ty} (c : LifeVar)
    {T : Ty} (hT : plainB T = true) (hc : Δ.find? c = none) (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ (withborS σ) (wTy Places.immM c Δ.meetOfDom σ T) :=
  withborS_wf formerImm hσ c hT hc hΓ

end BoCa.LeafPlaces

end
