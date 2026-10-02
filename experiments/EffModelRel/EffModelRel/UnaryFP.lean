import EffModelRel.ModedJ

/-!
# EffModelRel — unary resource safety

The fundamental property of the unary relation (`CM.fp`): a moded term, in an environment whose
values own `Os`, is safe owning exactly what its linear variables own. For a closed program it
owns nothing, and `adequacyU` turns that into a run that never fails an action and, if it
returns, has every finaliser run once and every capability consumed (`resource_safety`).
-/

namespace EffRel

variable {S : Sig}

/-! ## Environments of owned values -/

def EnvS (ρ : Env (S := S) Γ) (Os : (A : VTy S) → Var Γ A → Own) : Prop :=
  ∀ A x, VS A (Os A x) (ρ A x)

def Own.envCons {B : VTy S} (O : Own) (Os : (A : VTy S) → Var Γ A → Own) :
    (A : VTy S) → Var (B :: Γ) A → Own
  | _, .z => O
  | _, .s x => Os _ x

theorem EnvS.cons {ρ : Env (S := S) Γ} {Os} (h : EnvS ρ Os) {B : VTy S} {O : Own} {b : B.den}
    (hb : VS B O b) : EnvS (ρ.cons b) (Own.envCons O Os) := by
  intro A x; cases x with
  | z => exact hb
  | s x => exact h _ x

theorem VS.zero_of {A : VTy S} {O : Own} {v : A.den} (h : VS A O v) (hl : A.isLin = false) :
    O = 0 := by
  apply VS.indep A h
  have : A.mode ≠ Mode.lin := by simpa [VTy.isLin] using hl
  revert this; generalize A.mode = m; intro hm
  obtain ⟨w, c⟩ := m; cases w <;> cases c <;> simp_all [Mode.lin]

theorem sumL_cons_val {A : VTy S} {Γ : List (VTy S)} {L : VSet Γ} {Os} {O : Own} {a : A.den}
    (h : VS A O a) : sumL (A :: Γ) (VSet.cons A.isLin L) (Own.envCons O Os) = O + sumL Γ L Os := by
  rw [sumL_cons]
  cases hl : A.isLin
  · rw [VS.zero_of h hl]; rfl
  · rfl

theorem sumL_cons_false {A : VTy S} {Γ : List (VTy S)} {L : VSet Γ} {Os} {O : Own} :
    sumL (A :: Γ) (VSet.cons false L) (Own.envCons O Os) = sumL Γ L Os := by
  rw [sumL_cons]; simp only [Bool.false_eq_true, if_false, Own.zero_add]; rfl

/-! ## Unfolding -/

theorem VS_g {g : G} {O : Own} {x : (VTy.g (S := S) g).den} : VS (.g g) O x ↔ O = 0 := by
  simp only [VS]
theorem VS_prod {A B : VTy S} {O : Own} {p : (VTy.prod A B).den} :
    VS (.prod A B) O p ↔ ∃ O₁ O₂, O = O₁ + O₂ ∧ VS A O₁ p.1 ∧ VS B O₂ p.2 := by simp only [VS]
theorem VS_inl {A B : VTy S} {O : Own} {a : A.den} : VS (.sum A B) O (.inl a) ↔ VS A O a := by
  simp only [VS]
theorem VS_inr {A B : VTy S} {O : Own} {b : B.den} : VS (.sum A B) O (.inr b) ↔ VS B O b := by
  simp only [VS]
theorem VS_U {m : Mode} {b : Eb} {C : CTy S} {O : Own} {c : C.den} :
    VS (.U m b C) O c ↔ (m.w = true ∨ m.c = true → O = 0) ∧ CS C (Bnd.const b.req) O c := by
  simp only [VS]
theorem VS_cap {e : S.E} {s : G} {O : Own} {c : (VTy.cap (S := S) e s).den} :
    VS (.cap e s) O c ↔ O = Own.one (.cap s) c.1 ∧
      ∀ o a st, TS (Bnd.const Mode.unr) (fun O' _ => O' = 0) 0 (c.2 o a st) := by simp only [VS]
theorem VS_res {O : Own} {x : (VTy.res (S := S)).den} : VS .res O x ↔ O = 0 := by simp only [VS]
theorem VS_strm {b : Eb} {A : VTy S} {O : Own} {s : (VTy.strm b A).den} :
    VS (.strm b A) O s ↔ StrmS (fun O a => VS A O a) (Bnd.const b.req) O s := by simp only [VS]

/-! ## Streams -/

theorem StrmLeafS.map {P P' : Own → Strm S X → Prop} {VA : Own → X → Prop}
    (h : ∀ O s, P O s → P' O s) : ∀ O x, StrmLeafS P VA O x → StrmLeafS P' VA O x
  | _, .inl _, hx => hx
  | _, .inr (_, _), hx => h _ _ hx

theorem StrmS.intro {VA : Own → X → Prop} {bnd : Bnd S} {O : Own} {p d}
    (hp : TS bnd (StrmLeafS (StrmS VA bnd) VA) O p) (hd : TS bnd (fun O' _ => O' = 0) O d) :
    StrmS VA bnd O (.mk p d) :=
  fun P hP => hP O p d (hp.mapP (StrmLeafS.map (fun _ _ hs => hs P hP))) hd

def StrmUnfS (VA : Own → X → Prop) (bnd : Bnd S) (O : Own) : Strm S X → Prop
  | .mk p d => TS bnd (StrmLeafS (StrmS VA bnd) VA) O p ∧ TS bnd (fun O' _ => O' = 0) O d

theorem StrmS.unf {VA : Own → X → Prop} {bnd : Bnd S} {O : Own} {s : Strm S X}
    (h : StrmS VA bnd O s) : StrmUnfS VA bnd O s := by
  apply h
  intro O p d hp hd
  refine ⟨hp.mapP (StrmLeafS.map (fun O s hs => ?_)), hd⟩
  cases s; exact StrmS.intro hs.1 hs.2

/-! ## Rows and bounds -/

theorem bndOf_le_const {Ψ : List S.E} {R : Row S Ψ} {m : Mode} (h : m.ge R.mode = true)
    (η : IEnv Ψ) : (bndOf η R).le (Bnd.const m) := fun j e => Mode.ge_trans h (R.mode_ge η j e)

theorem CS.mono_row {C : CTy S} {Ψ : List S.E} {R R' : Row S Ψ} {η : IEnv Ψ} {O : Own} {c : C.den}
    (h : CS C (bndOf η R) O c) (hs : R.Sub R') : CS C (bndOf η R') O c :=
  CS.mono C h (bndOf_sub hs η)

theorem bndOf_join_fgn {Ψ : List S.E} (R : Row S Ψ) (η : IEnv Ψ) (m : Mode) :
    ((bndOf η R).join m).le (bndOf η (R.union (Row.fgn m))) := fun j e =>
  Mode.join_ge (bndOf_sub (Row.sub_union_l R (Row.fgn m)) η j e)
    (Mode.ge_trans (bndOf_ge_fb (R.union (Row.fgn m)) η j e) (Mode.ge_join_r R.fb m))

theorem ground_zero {g : G} {L : VSet Γ} {O : Own} {x : (VTy.g (S := S) g).den}
    (h : VS (.g g) O x) : O = 0 := VS_g.1 h

theorem Bnd.lin_isLin : (Bnd.const (S := S) Mode.lin).IsLin := fun _ _ => Mode.isLin_lin

theorem VS_coRes_zero {e : S.E} {s : G} {o : S.O e} {O : Own} {x : (coRes S e s o).den}
    (h : VS (coRes S e s o) O x) : O = 0 := by
  unfold coRes at x h
  rcases x with ⟨a, b⟩ | ⟨a, b⟩
  · obtain ⟨O₁, O₂, rfl, h1, h2⟩ := VS_prod.1 (VS_inl.1 h)
    rw [VS_g.1 h1, VS_g.1 h2, Own.zero_add]
  · obtain ⟨O₁, O₂, rfl, h1, h2⟩ := VS_prod.1 (VS_inr.1 h)
    rw [VS_g.1 h1, VS_g.1 h2, Own.zero_add]

theorem Bnd.le_unr (b : Bnd S) : b.le (Bnd.const Mode.unr) := fun _ _ => by
  simp only [Bnd.const, Mode.ge, Mode.unr]; simp

theorem bndOf_c {Ψ : List S.E} {R : Row S Ψ} (h : R.mode.c = false) (η : IEnv Ψ) :
    ∀ j e, (bndOf η R j e).c = false := fun j e => by
  have := R.mode_ge η j e
  revert this; generalize bndOf η R j e = m; intro hm
  obtain ⟨w, c⟩ := m; obtain ⟨w', c'⟩ := R.mode
  cases c <;> simp_all [Mode.ge]

/-! ## The fundamental property

By recursion on the term, inverting the judgement at each former. -/

mutual
theorem VM.fp {Ψ : List S.E} {Γ : List (VTy S)} : {A : VTy S} → (v : Val S Ψ Γ A) →
    ∀ {L : VSet Γ}, VM L v → ∀ (η : IEnv Ψ) (ρ : Env Γ) (Os : (B : VTy S) → Var Γ B → Own),
    EnvS ρ Os → VS A (sumL Γ L Os) (v.den η ρ)
  | _, .var x, _, h, η, ρ, Os, hρ => by
      cases h
      simp only [Val.den]
      cases hl : (VTy.isLin _)
      · simp only [Bool.false_eq_true, if_false]; rw [sumL_none]
        have := hρ _ x; rwa [VS.zero_of this hl] at this
      · simp only [if_true]; rw [sumL_single]; exact hρ _ x
  | _, .unit, _, h, _, _, Os, _ => by cases h; rw [sumL_none]; exact VS_g.2 rfl
  | _, .int _, _, h, _, _, Os, _ => by cases h; rw [sumL_none]; exact VS_g.2 rfl
  | _, .bool _, _, h, _, _, Os, _ => by cases h; rw [sumL_none]; exact VS_g.2 rfl
  | _, .pair a b, _, h, η, ρ, Os, hρ => by
      cases h with
      | pair ha hb hd =>
          rw [sumL_union _ _ hd]
          exact VS_prod.2 ⟨_, _, rfl, VM.fp a ha η ρ Os hρ, VM.fp b hb η ρ Os hρ⟩
  | _, .inl a, _, h, η, ρ, Os, hρ => by
      cases h with | inl ha => exact VS_inl.2 (VM.fp a ha η ρ Os hρ)
  | _, .inr b, _, h, η, ρ, Os, hρ => by
      cases h with | inr hb => exact VS_inr.2 (VM.fp b hb η ρ Os hρ)
  | _, .thunk _ M, _, h, η, ρ, Os, hρ => by
      cases h with
      | thunk m b hM hm hb =>
          refine VS_U.2 ⟨fun h' => sumL_empty (hm h') Os, ?_⟩
          exact CS.mono _ (CM.fp M hM η ρ Os hρ) (bndOf_le_const hb η)
  | _, .fold v, _, h, η, ρ, Os, hρ => by
      cases h with
      | fold hv =>
          have h0 := CS_wth.1 (VS_U.1 (VM.fp v hv η ρ Os hρ)).2
          simp only [Val.den]
          refine VS_strm.2 (StrmS.intro ((CS_F.1 h0.1).mapP (fun O x hx => ?_))
            ((CS_F.1 h0.2).mapP (fun O _ hx => VS_g.1 hx)))
          rcases x with a | ⟨n, s⟩
          · exact VS_inl.1 hx
          · obtain ⟨O₁, O₂, rfl, h1, h2⟩ := VS_prod.1 (VS_inr.1 hx)
            rw [VS_g.1 h1, Own.zero_add]; exact VS_strm.1 h2

theorem CM.fp {Ψ : List S.E} {Γ : List (VTy S)} : {C : CTy S} → (M : Cmp S Ψ Γ C) →
    ∀ {L : VSet Γ} {R : Row S Ψ}, CM L R M → ∀ (η : IEnv Ψ) (ρ : Env Γ)
    (Os : (B : VTy S) → Var Γ B → Own), EnvS ρ Os → CS C (bndOf η R) (sumL Γ L Os) (M.den η ρ)
  | _, .ret v, _, _, h, η, ρ, Os, hρ => by
      cases h with | ret hv => exact CS_F.2 (.ret (VM.fp v hv η ρ Os hρ))
  | _, .bind M N, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | bind hM hN hd hc =>
          rw [sumL_union _ _ hd]
          simp only [Cmp.den]
          refine bindC_safe _ (CS_F.1 (CM.fp M hM η ρ Os hρ)) (fun O' x hx => ?_) ?_
            (bndOf_sub (Row.sub_union_l _ _) η)
          · have := CM.fp N hN η (ρ.cons x) (Own.envCons O' Os) (hρ.cons hx)
            rw [sumL_cons_val hx] at this
            exact this.mono_row (Row.sub_union_r _ _)
          · rcases hc with he | hl
            · exact .inl (sumL_empty he Os)
            · exact .inr (Row.isLin_bnd hl η)
  | _, .lam M, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | lam hM hb =>
          refine CS_arr.2 (fun Oa a ha _ => ?_)
          have := CM.fp M hM η (ρ.cons a) (Own.envCons Oa Os) (hρ.cons ha)
          rw [sumL_cons_val ha, Own.add_comm] at this
          refine CS.mono _ this (fun j e => ?_)
          simp only [Bnd.join, bndOf_none, Bnd.const, Mode.lin_join]
          exact Mode.ge_trans hb (Row.mode_ge _ η j e)
  | _, .app M v, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | app hM hv hd hc =>
          rw [sumL_union _ _ hd]
          simp only [Cmp.den]
          refine CS.mono _ (CS_arr.1 (CM.fp M hM η ρ Os hρ) _ _ (VM.fp v hv η ρ Os hρ) ?_)
            (bndOf_join_fgn _ η _)
          rcases hc with he | hl
          · exact .inl (sumL_empty he Os)
          · exact .inr (Row.isLin_bnd hl η)
  | _, .force v, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | force hv => rw [bndOf_fgn]; exact (VS_U.1 (VM.fp v hv η ρ Os hρ)).2
  | _, .rcd M N, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | rcd hM hN =>
          exact CS_wth.2 ⟨(CM.fp M hM η ρ Os hρ).mono_row (Row.sub_union_l _ _),
            (CM.fp N hN η ρ Os hρ).mono_row (Row.sub_union_r _ _)⟩
  | _, .prj1 M, _, _, h, η, ρ, Os, hρ => by
      cases h with | prj1 hM => exact (CS_wth.1 (CM.fp M hM η ρ Os hρ)).1
  | _, .prj2 M, _, _, h, η, ρ, Os, hρ => by
      cases h with | prj2 hM => exact (CS_wth.1 (CM.fp M hM η ρ Os hρ)).2
  | _, .split v M, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | split hv hM hd =>
          rw [sumL_union _ _ hd]
          obtain ⟨O₁, O₂, h12, h1, h2⟩ := VS_prod.1 (VM.fp v hv η ρ Os hρ)
          simp only [Cmp.den]
          have := CM.fp M hM η ((ρ.cons (v.den η ρ).1).cons (v.den η ρ).2)
            (Own.envCons O₂ (Own.envCons O₁ Os)) ((hρ.cons h1).cons h2)
          rw [sumL_cons_val h2, sumL_cons_val h1] at this
          rw [h12, show O₁ + O₂ + sumL Γ _ Os = O₂ + (O₁ + sumL Γ _ Os) by
            rw [Own.add_comm O₁ O₂, Own.add_assoc]]
          exact this
  | _, .case v M N, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | case hv hM hN hd =>
          rw [sumL_union _ _ hd]
          have hvs := VM.fp v hv η ρ Os hρ
          simp only [Cmp.den]
          generalize v.den η ρ = x at hvs ⊢
          rcases x with a | b
          · have := CM.fp M hM η (ρ.cons a) (Own.envCons _ Os) (hρ.cons (VS_inl.1 hvs))
            rw [sumL_cons_val (VS_inl.1 hvs)] at this
            exact this.mono_row (Row.sub_union_l _ _)
          · have := CM.fp N hN η (ρ.cons b) (Own.envCons _ Os) (hρ.cons (VS_inr.1 hvs))
            rw [sumL_cons_val (VS_inr.1 hvs)] at this
            exact this.mono_row (Row.sub_union_r _ _)
  | _, .ite v M N, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | ite hv hM hN hd =>
          rw [sumL_union _ _ hd, VS_g.1 (VM.fp v hv η ρ Os hρ), Own.zero_add]
          simp only [Cmp.den]
          cases (v.den η ρ : Bool)
          · exact (CM.fp N hN η ρ Os hρ).mono_row (Row.sub_union_r _ _)
          · exact (CM.fp M hM η ρ Os hρ).mono_row (Row.sub_union_l _ _)
  | _, .absurd v, _, _, _, η, ρ, _, _ => (v.den η ρ : Empty).elim
  | _, .prim p a b, _, _, h, η, ρ, Os, hρ => by
      have key : ∀ {L₁ L₂ : VSet Γ}, VM L₁ a → VM L₂ b → L₁.Disj L₂ →
          CS (.F (.g p.res)) (bndOf η Row.none) (sumL Γ (L₁.union L₂) Os) ((Cmp.prim p a b).den η ρ) :=
        fun ha hb hd => by
          rw [sumL_union _ _ hd, VS_g.1 (VM.fp a ha η ρ Os hρ), VS_g.1 (VM.fp b hb η ρ Os hρ),
            Own.zero_add]
          exact CS_F.2 (.ret (VS_g.2 rfl))
      cases p <;> cases h <;> exact key ‹_› ‹_› ‹_›
  | _, .emit v, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | emit hv =>
          rw [VS_g.1 (VM.fp v hv η ρ Os hρ)]
          exact CS_F.2 (.act .out (fun _ => .ret (VS_g.2 rfl)))
  | _, .op x o v M, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | op _ _ hv hM hd hc =>
          rw [sumL_union _ _ hd, VS_g.1 (VM.fp v hv η ρ Os hρ), Own.zero_add]
          simp only [Cmp.den]
          refine opA_safe _ ?_ ?_ (fun y => ?_)
          · exact Mode.ge_trans (bndOf_sub (Row.sub_union_l _ _) η _ _)
              (Mode.ge_trans (bndOf_inst η x) (S.bnd_q _ o))
          · rcases hc with he | hl
            · rw [sumL_empty he]; exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => .nil⟩
            · exact ⟨fun hcc => absurd hcc (by simp [hl.2]), fun hw => absurd hw (by simp [hl.1])⟩
          · have := CM.fp M hM η (ρ.cons (VTy.gv y)) (Own.envCons 0 Os) (hρ.cons (VS_g.2 rfl))
            rw [sumL_cons_false] at this
            exact this.mono_row (Row.sub_union_r _ _)
  | _, .ab x a v, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | ab _ _ hv =>
          rw [VS_g.1 (VM.fp v hv η ρ Os hρ)]
          exact abA_safe _ (Mode.ge_trans (bndOf_inst η x) (S.bnd_ab _ a)) .nil
  | _, .handle e bk hr hop hab B, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | handle _ _ hB Rr hhr hRr Ro hhop hRo Ra hhab hRa hd hOH hfwd hbk =>
          rw [sumL_union _ _ hd]
          simp only [Cmp.den]
          refine nuA_safe _ (fun i => ?_)
          refine hnd_safe _ (CS_F.1 (CM.fp B hB (η.cons i) ρ Os hρ)) ?_ ?_ ?_
            (hOH.imp (sumL_empty · Os) id) ?_ ?_ (bndOf_le_const hbk η)
          · intro O' x hx
            have := CM.fp hr hhr η (ρ.cons x) (Own.envCons O' Os) (hρ.cons hx)
            rw [sumL_cons_val hx] at this
            exact this.mono_row (Row.sub_trans hRr (Row.sub_union_r _ _))
          · intro o v Oκ k d hκ
            have := CM.fp (hop o) (hhop o) η ((ρ.cons (VTy.gv v)).cons _)
              (Own.envCons Oκ (Own.envCons 0 Os)) ((hρ.cons (VS_g.2 rfl)).cons hκ)
            rw [sumL_cons_val hκ, sumL_cons_false, sumL_none, Own.add_zero] at this
            exact this.mono_row (Row.sub_trans (hRo o) (Row.sub_union_r _ _))
          · intro a v
            have := CM.fp (hab a) (hhab a) η (ρ.cons (VTy.gv v)) (Own.envCons 0 Os)
              (hρ.cons (VS_g.2 rfl))
            rw [sumL_cons_false] at this
            exact this.mono_row (Row.sub_trans (hRa a) (Row.sub_union_r _ _))
          · rcases hfwd with he | hl
            · exact .inl (sumL_empty he Os)
            · refine .inr (fun j e' hne => ?_)
              rw [bndOf_cons _ η i j e' (.inl hne)]
              exact Row.isLin_bnd hl η j e'
          · intro j e' hne
            rw [bndOf_cons _ η i j e' (.inl hne)]
            exact bndOf_sub (Row.sub_union_l _ _) η j e'
  | _, .handleAt x bk hr hop hab B, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | handleAt _ _ hB Rr hhr hRr Ro hhop hRo Ra hhab hRa hd hOH hfwd hbk =>
          rw [sumL_union _ _ hd]
          simp only [Cmp.den]
          refine hnd_safe _ (CS_F.1 (CM.fp B hB η ρ Os hρ)) ?_ ?_ ?_
            (hOH.imp (sumL_empty · Os) id) ?_ ?_ (bndOf_le_const hbk η)
          · intro O' x hx
            have := CM.fp hr hhr η (ρ.cons x) (Own.envCons O' Os) (hρ.cons hx)
            rw [sumL_cons_val hx] at this
            exact this.mono_row (Row.sub_trans hRr (Row.sub_union_r _ _))
          · intro o v Oκ k d hκ
            have := CM.fp (hop o) (hhop o) η ((ρ.cons (VTy.gv v)).cons _)
              (Own.envCons Oκ (Own.envCons 0 Os)) ((hρ.cons (VS_g.2 rfl)).cons hκ)
            rw [sumL_cons_val hκ, sumL_cons_false, sumL_none, Own.add_zero] at this
            exact this.mono_row (Row.sub_trans (hRo o) (Row.sub_union_r _ _))
          · intro a v
            have := CM.fp (hab a) (hhab a) η (ρ.cons (VTy.gv v)) (Own.envCons 0 Os)
              (hρ.cons (VS_g.2 rfl))
            rw [sumL_cons_false] at this
            exact this.mono_row (Row.sub_trans (hRa a) (Row.sub_union_r _ _))
          · rcases hfwd with he | hl
            · exact .inl (sumL_empty he Os)
            · exact .inr (fun j e' _ => Row.isLin_bnd hl η j e')
          · intro j e' _
            exact bndOf_sub (Row.sub_union_l _ _) η j e'
  | _, .nu e M, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | nu _ hM hz =>
          simp only [Cmp.den]
          refine nuA_safe _ (fun i => ?_)
          have := CM.fp M hM (η.cons i) ρ Os hρ
          have hb : bndOf (η.cons i) _ = bndOf η _ := funext fun j => funext fun e' =>
            bndOf_cons _ η i j e' (.inr hz)
          rwa [hb] at this
  | _, .ieq x y, _, _, h, η, ρ, Os, hρ => by
      cases h; rw [sumL_none]; exact CS_F.2 (.ret (VS_g.2 rfl))
  | _, .ilam M, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | ilam hM =>
          refine CS_pi.2 (fun i => ?_)
          exact CS.mono _ (CM.fp M hM (η.cons i) ρ Os hρ) (bndOf_cons_le _ η i)
  | _, .iapp M x, _, _, h, η, ρ, Os, hρ => by
      cases h with | iapp _ hM => exact CS_pi.1 (CM.fp M hM η ρ Os hρ) (η _ x)
  | _, .newcap e s co v, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | newcap _ _ hv Rc hco =>
          rw [VS_g.1 (VM.fp v hv η ρ Os hρ)]
          simp only [Cmp.den]
          refine CS_F.2 (.nuNew (fun n _ => .ret ?_))
          refine VS_cap.2 ⟨by simp [VTy.capv], fun o a st => ?_⟩
          have := CM.fp (co o) (hco o) IEnv.nil ((Env.nil.cons (VTy.gv a)).cons (VTy.gv st))
            (fun _ _ => 0) (by intro B z; rcases z with _ | _ | z <;> first | exact VS_g.2 rfl | exact nomatch z)
          rw [sumL_none] at this
          exact ((CS_F.1 this).mono (Bnd.le_unr _)).mapP (fun _ _ h => VS_coRes_zero h)
  | _, .getcap v, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | getcap hv =>
          obtain ⟨hO, _⟩ := VS_cap.1 (VM.fp v hv η ρ Os hρ)
          simp only [Cmp.den]
          rw [hO, ← Own.zero_add (Own.one _ _)]
          exact CS_F.2 (.act .kill (fun _ => .ret (VS_g.2 rfl)))
  | _, .using ℓ M, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | «using» _ hM hc =>
          simp only [Cmp.den]
          refine CS_F.2 (.nuAcq (fun n _ => ?_))
          have := CM.fp M hM η (ρ.cons (VTy.resv ℓ n)) (Own.envCons 0 Os) (hρ.cons (VS_res.2 rfl))
          rw [sumL_cons_false] at this
          exact addFin_safe (CS_F.1 this) (bndOf_c hc η) ℓ n
  | _, .lend v M, _, _, h, _, _, _, _ => by cases h
  | _, .use v, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | use hv =>
          rw [VS_res.1 (VM.fp v hv η ρ Os hρ)]
          exact CS_F.2 (.act .use (fun _ => .ret (VS_g.2 rfl)))
  | _, .unfold v, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | unfold hv =>
          have hs := VS_strm.1 (VM.fp v hv η ρ Os hρ)
          simp only [Cmp.den]
          rw [bndOf_fgn]
          generalize v.den η ρ = st at hs ⊢
          rcases st with ⟨p, d⟩
          have hu := hs.unf
          refine CS_wth.2 ⟨CS_F.2 (hu.1.mapP fun O x hx => ?_),
            CS_F.2 (hu.2.mapP fun O _ hx => VS_g.2 hx)⟩
          rcases x with a | ⟨n, st⟩
          · exact VS_inl.2 hx
          · exact VS_inr.2 (VS_prod.2 ⟨0, O, by simp, VS_g.2 rfl, VS_strm.2 hx⟩)
  | _, .bfix x a v n M, _, _, h, η, ρ, Os, hρ => by
      cases h with
      | bfix _ _ _ hv hM hb =>
          rw [sumL_none]
          simp only [Cmp.den]
          induction n with
          | zero =>
              exact abA_safe _ (Mode.ge_trans (bndOf_sub (Row.sub_union_l _ _) η _ _)
                (Mode.ge_trans (bndOf_inst η x) (S.bnd_ab _ a))) .nil
          | succ n ih =>
              have := CM.fp M hM η (ρ.cons (VTy.uv _)) (Own.envCons 0 Os)
                (hρ.cons (VS_U.2 ⟨fun _ => rfl, CS.mono _ ih (bndOf_le_const hb η)⟩))
              rw [sumL_cons_false, sumL_none] at this
              exact this.mono_row (Row.sub_union_r _ _)
end

/-! ## Resource safety -/

/-- **Unary resource safety.** A moded closed program, run against the world with a ghost count
of live tokens, never fails an action: every free, read, write and consume finds its token, and
every cell it touches is live. If it returns, nothing is live: every resource a `using` frame
acquired was freed exactly once (on return, on abort, or when a continuation holding the frame
was cancelled or a stream was dropped), and every capability was consumed exactly once. -/
theorem resource_safety {g : G} (P : Prog S g) {R : Row S []}
    (hP : CM (Ψ := []) (Γ := []) VSet.none R P) :
    (P.den IEnv.nil Env.nil).Safe (fun O _ => O = 0) ⟨Wd.init, 0⟩ := by
  have h := CM.fp P hP IEnv.nil Env.nil (fun _ _ => 0) (fun _ x => nomatch x)
  exact adequacyU ((CS_F.1 h).mapP (fun O _ hv => VS_g.1 hv)) _
    ⟨rfl, fun _ _ h0 => absurd rfl h0, fun _ _ _ => ⟨rfl, rfl⟩⟩

end EffRel
