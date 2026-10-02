import EffModelRel.ModedJ

/-!
# EffModelRel — unary resource and effect safety

The fundamental property of the unary relation (`CM.fp`): a moded term, in an environment whose
values own `Os`, is safe owning exactly what its linear variables own, and performs only on the
instances of its row. For a closed program it owns nothing and may perform on nothing, and
`adequacyU` turns that into a run that never fails an action, in which no operation reaches the
top, and which, if it returns, has every finaliser run once and every capability consumed
(`safety`). The run returns (`safety_obs`): trees are finite.
-/

namespace EffRel

variable {S : Sig}

/-! ## Environments of owned values -/

def EnvS (θ : LEnv S) (ρ : Env (S := S) Γ) (Os : (A : VTy S) → Var Γ A → Own) : Prop :=
  ∀ A x, VS A θ (Os A x) (ρ A x)

/-- Every type of the context is scoped under `n` instances. -/
def ΓSc (Γ : List (VTy S)) (n : Nat) : Prop := ∀ A (x : Var Γ A), A.Sc n

theorem ΓSc.cons {Γ : List (VTy S)} {n : Nat} (h : ΓSc Γ n) {A : VTy S} (hA : A.Sc n) :
    ΓSc (A :: Γ) n := by
  intro B x; cases x with
  | z => exact hA
  | s x => exact h _ x

theorem ΓSc.mono {Γ : List (VTy S)} {n : Nat} (h : ΓSc Γ n) : ΓSc Γ (n + 1) :=
  fun A x => VTy.Sc.mono (Nat.le_succ n) A (h A x)

def Own.envCons {B : VTy S} (O : Own) (Os : (A : VTy S) → Var Γ A → Own) :
    (A : VTy S) → Var (B :: Γ) A → Own
  | _, .z => O
  | _, .s x => Os _ x

theorem EnvS.cons {θ : LEnv S} {ρ : Env (S := S) Γ} {Os} (h : EnvS θ ρ Os) {B : VTy S} {O : Own}
    {b : B.den} (hb : VS B θ O b) : EnvS θ (ρ.cons b) (Own.envCons O Os) := by
  intro A x; cases x with
  | z => exact hb
  | s x => exact h _ x

theorem VS.zero_of {A : VTy S} {θ : LEnv S} {O : Own} {v : A.den} (h : VS A θ O v)
    (hl : A.isLin = false) : O = 0 := by
  apply VS.indep A h
  have : A.mode ≠ Mode.lin := by simpa [VTy.isLin] using hl
  revert this; generalize A.mode = m; intro hm
  obtain ⟨w, c⟩ := m; cases w <;> cases c <;> simp_all [Mode.lin]

theorem sumL_cons_val {A : VTy S} {θ : LEnv S} {Γ : List (VTy S)} {L : VSet Γ} {Os} {O : Own}
    {a : A.den} (h : VS A θ O a) :
    sumL (A :: Γ) (VSet.cons A.isLin L) (Own.envCons O Os) = O + sumL Γ L Os := by
  rw [sumL_cons]
  cases hl : A.isLin
  · rw [VS.zero_of h hl]; rfl
  · rfl

theorem sumL_cons_false {A : VTy S} {Γ : List (VTy S)} {L : VSet Γ} {Os} {O : Own} :
    sumL (A :: Γ) (VSet.cons false L) (Own.envCons O Os) = sumL Γ L Os := by
  rw [sumL_cons]; simp only [Bool.false_eq_true, if_false, Own.zero_add]; rfl

/-! ## Unfolding -/

theorem VS_g {g : G} {θ : LEnv S} {O : Own} {x : (VTy.g (S := S) g).den} :
    VS (.g g) θ O x ↔ O = 0 := by simp only [VS]
theorem VS_prod {A B : VTy S} {θ : LEnv S} {O : Own} {p : (VTy.prod A B).den} :
    VS (.prod A B) θ O p ↔ ∃ O₁ O₂, O = O₁ + O₂ ∧ VS A θ O₁ p.1 ∧ VS B θ O₂ p.2 := by
  simp only [VS]
theorem VS_inl {A B : VTy S} {θ : LEnv S} {O : Own} {a : A.den} :
    VS (.sum A B) θ O (.inl a) ↔ VS A θ O a := by simp only [VS]
theorem VS_inr {A B : VTy S} {θ : LEnv S} {O : Own} {b : B.den} :
    VS (.sum A B) θ O (.inr b) ↔ VS B θ O b := by simp only [VS]
theorem VS_U {m : Mode} {b : Rw} {C : CTy S} {θ : LEnv S} {O : Own} {c : C.den} :
    VS (.U m b C) θ O c ↔ (m.w = true ∨ m.c = true → O = 0) ∧ CS C θ (b.ok θ) O c := by
  simp only [VS]
theorem VS_cap {e : S.E} {s : G} {θ : LEnv S} {O : Own} {c : (VTy.cap (S := S) e s).den} :
    VS (.cap e s) θ O c ↔ O = Own.one (.cap s) c.1 ∧ (S.A e → False) ∧
      ∀ o a st, TS Ok.bot (fun O' _ => O' = 0) 0 (c.2 o a st) := by simp only [VS]
theorem VS_strm {b : Rw} {A : VTy S} {θ : LEnv S} {O : Own} {s : (VTy.strm b A).den} :
    VS (.strm b A) θ O s ↔ StrmS (fun O a => VS A θ O a) (b.ok θ) O s := by simp only [VS]

/-! ## A type's relation does not see instances beyond its scope -/

mutual
theorem VS_ext {θ : LEnv S} (p : Nat × S.E) : (A : VTy S) → A.Sc θ.length →
    VS A (θ ++ [p]) = VS A θ
  | .g _, _ => by funext O v; simp only [VS]
  | .prod A B, h => by
      funext O v; simp only [VS]; rw [VS_ext p A h.1, VS_ext p B h.2]
  | .sum A B, h => by
      funext O v; cases v with
      | inl a => simp only [VS]; rw [VS_ext p A h.1]
      | inr b => simp only [VS]; rw [VS_ext p B h.2]
  | .U _ _ C, h => by
      funext O v; simp only [VS]; rw [CS_ext p C h.2, Rw.ok_ext h.1]
  | .cap _ _, _ => by funext O v; simp only [VS]
  | .strm _ A, h => by
      funext O v; simp only [VS]; rw [VS_ext p A h.2, Rw.ok_ext h.1]
theorem CS_ext {θ : LEnv S} (p : Nat × S.E) : (C : CTy S) → C.Sc θ.length →
    CS C (θ ++ [p]) = CS C θ
  | .F A, h => by funext ok O t; simp only [CS]; rw [VS_ext p A h]
  | .arr A _ C, h => by
      funext ok O f; simp only [CS]; rw [VS_ext p A h.1, CS_ext p C h.2.2, Rw.ok_ext h.2.1]
  | .wth C D, h => by funext ok O x; simp only [CS]; rw [CS_ext p C h.1, CS_ext p D h.2]
  | .pi _ C, h => by funext ok O f; simp only [CS]; rw [CS_ext p C h]
end

theorem EnvS.ext {θ : LEnv S} {ρ : Env (S := S) Γ} {Os} (h : EnvS θ ρ Os) (hΓ : ΓSc Γ θ.length)
    (p : Nat × S.E) : EnvS (θ ++ [p]) ρ Os := fun A x => by rw [VS_ext p A (hΓ A x)]; exact h A x

/-! ## Streams -/

theorem StrmLeafS.map {P P' : Own → Strm S X → Prop} {VA : Own → X → Prop}
    (h : ∀ O s, P O s → P' O s) : ∀ O x, StrmLeafS P VA O x → StrmLeafS P' VA O x
  | _, .inl _, hx => hx
  | _, .inr (_, _), hx => h _ _ hx

theorem StrmS.intro {VA : Own → X → Prop} {ok : Ok S} {O : Own} {p d}
    (hp : TS ok (StrmLeafS (StrmS VA ok) VA) O p) (hd : TS ok (fun O' _ => O' = 0) O d) :
    StrmS VA ok O (.mk p d) :=
  fun P hP => hP O p d (hp.mapP (StrmLeafS.map (fun _ _ hs => hs P hP))) hd

def StrmUnfS (VA : Own → X → Prop) (ok : Ok S) (O : Own) : Strm S X → Prop
  | .mk p d => TS ok (StrmLeafS (StrmS VA ok) VA) O p ∧ TS ok (fun O' _ => O' = 0) O d

theorem StrmS.unf {VA : Own → X → Prop} {ok : Ok S} {O : Own} {s : Strm S X}
    (h : StrmS VA ok O s) : StrmUnfS VA ok O s := by
  apply h
  intro O p d hp hd
  refine ⟨hp.mapP (StrmLeafS.map (fun O s hs => ?_)), hd⟩
  cases s; exact StrmS.intro hs.1 hs.2

/-! ## Rows -/

theorem CS.mono_row {C : CTy S} {θ : LEnv S} {Ψ : List S.E} {R R' : Row S Ψ} {η : IEnv Ψ}
    {O : Own} {c : C.den} (h : CS C θ (okOf η R) O c) (hs : R.Sub R') : CS C θ (okOf η R') O c :=
  CS.mono C h (okOf_sub hs η)

/-- What a row's type permits covers what a smaller row permits. -/
theorem okOf_le_row {Ψ : List S.E} {R : Row S Ψ} {b : Rw} (h : R.Sub (b.row Ψ)) (η : IEnv Ψ) :
    (okOf η R).le (b.ok η.lv) := by
  rw [← okOf_row]; exact okOf_sub h η

theorem VS_coRes_zero {e : S.E} {s : G} {o : S.O e} {θ : LEnv S} {O : Own}
    {x : (coRes S e s o).den} (h : VS (coRes S e s o) θ O x) : O = 0 := by
  unfold coRes at x h
  rcases x with ⟨a, b⟩ | ⟨a, b⟩
  · obtain ⟨O₁, O₂, rfl, h1, h2⟩ := VS_prod.1 (VS_inl.1 h)
    rw [VS_g.1 h1, VS_g.1 h2, Own.zero_add]
  · obtain ⟨O₁, O₂, rfl, h1, h2⟩ := VS_prod.1 (VS_inr.1 h)
    rw [VS_g.1 h1, VS_g.1 h2, Own.zero_add]

theorem okOf_nil (R : Row S []) : okOf IEnv.nil R = Ok.bot := by
  funext j e; simp [okOf, hits, Ok.bot]

theorem kty_sc {q : Mode} {bk : Rw} {r : G} {C : CTy S} {n : Nat} (hb : bk.Sc n) (hC : C.Sc n) :
    (kty q bk r C).Sc n := by
  obtain ⟨w, c⟩ := q
  cases w <;> exact ⟨fun _ h => by simp [Rw.nil] at h, by
    first
    | exact ⟨⟨trivial, hb, hC⟩, trivial⟩
    | exact ⟨trivial, hb, hC⟩⟩

theorem coRes_sc {e : S.E} {s : G} {o : S.O e} {n : Nat} : (coRes S e s o).Sc n :=
  ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-! ## The fundamental property

By recursion on the term, inverting the judgement at each former. -/

mutual
theorem VM.fp {Ψ : List S.E} {Γ : List (VTy S)} : {A : VTy S} → (v : Val S Ψ Γ A) →
    ∀ {L : VSet Γ}, VM L v → A.Sc Ψ.length → ΓSc Γ Ψ.length → ∀ (η : IEnv Ψ) (ρ : Env Γ)
    (Os : (B : VTy S) → Var Γ B → Own), EnvS η.lv ρ Os → VS A η.lv (sumL Γ L Os) (v.den η ρ)
  | _, .var x, _, h, _, _, η, ρ, Os, hρ => by
      cases h
      simp only [Val.den]
      cases hl : (VTy.isLin _)
      · simp only [Bool.false_eq_true, if_false]; rw [sumL_none]
        have := hρ _ x; rwa [VS.zero_of this hl] at this
      · simp only [if_true]; rw [sumL_single]; exact hρ _ x
  | _, .unit, _, h, _, _, _, _, Os, _ => by cases h; rw [sumL_none]; exact VS_g.2 rfl
  | _, .int _, _, h, _, _, _, _, Os, _ => by cases h; rw [sumL_none]; exact VS_g.2 rfl
  | _, .bool _, _, h, _, _, _, _, Os, _ => by cases h; rw [sumL_none]; exact VS_g.2 rfl
  | _, .pair a b, _, h, hA, hΓ, η, ρ, Os, hρ => by
      cases h with
      | pair ha hb hd =>
          rw [sumL_union _ _ hd]
          exact VS_prod.2 ⟨_, _, rfl, VM.fp a ha hA.1 hΓ η ρ Os hρ, VM.fp b hb hA.2 hΓ η ρ Os hρ⟩
  | _, .inl a, _, h, hA, hΓ, η, ρ, Os, hρ => by
      cases h with | inl ha => exact VS_inl.2 (VM.fp a ha hA.1 hΓ η ρ Os hρ)
  | _, .inr b, _, h, hA, hΓ, η, ρ, Os, hρ => by
      cases h with | inr hb => exact VS_inr.2 (VM.fp b hb hA.2 hΓ η ρ Os hρ)
  | _, .thunk _ M, _, h, hA, hΓ, η, ρ, Os, hρ => by
      cases h with
      | thunk m b hM hm hb =>
          refine VS_U.2 ⟨fun h' => sumL_empty (hm h') Os, ?_⟩
          exact CS.mono _ (CM.fp M hM hA.2 hΓ η ρ Os hρ) (okOf_le_row hb η)
  | _, .fold v, _, h, hA, hΓ, η, ρ, Os, hρ => by
      cases h with
      | fold hv =>
          have h0 := CS_wth.1 (VS_U.1 (VM.fp v hv ⟨hA.1, ⟨⟨hA.2, trivial, hA.1, hA.2⟩, trivial⟩⟩
            hΓ η ρ Os hρ)).2
          simp only [Val.den]
          refine VS_strm.2 (StrmS.intro ((CS_F.1 h0.1).mapP (fun O x hx => ?_))
            ((CS_F.1 h0.2).mapP (fun O _ hx => VS_g.1 hx)))
          rcases x with a | ⟨n, s⟩
          · exact VS_inl.1 hx
          · obtain ⟨O₁, O₂, rfl, h1, h2⟩ := VS_prod.1 (VS_inr.1 hx)
            rw [VS_g.1 h1, Own.zero_add]; exact VS_strm.1 h2

theorem CM.fp {Ψ : List S.E} {Γ : List (VTy S)} : {C : CTy S} → (M : Cmp S Ψ Γ C) →
    ∀ {L : VSet Γ} {R : Row S Ψ}, CM L R M → C.Sc Ψ.length → ΓSc Γ Ψ.length →
    ∀ (η : IEnv Ψ) (ρ : Env Γ) (Os : (B : VTy S) → Var Γ B → Own), EnvS η.lv ρ Os →
    CS C η.lv (okOf η R) (sumL Γ L Os) (M.den η ρ)
  | _, .ret v, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with | ret hv => exact CS_F.2 (.ret (VM.fp v hv hC hΓ η ρ Os hρ))
  | _, .bind M N, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | bind hM hN hd hc hA =>
          rw [sumL_union _ _ hd]
          simp only [Cmp.den]
          refine bindC_safe _ (CS_F.1 (CM.fp M hM hA hΓ η ρ Os hρ)) (fun O' x hx => ?_) ?_
            (okOf_sub (Row.sub_union_l _ _) η)
          · have := CM.fp N hN hC (hΓ.cons hA) η (ρ.cons x) (Own.envCons O' Os) (hρ.cons hx)
            rw [sumL_cons_val hx] at this
            exact this.mono_row (Row.sub_union_r _ _)
          · rcases hc with he | hl
            · exact .inl (sumL_empty he Os)
            · exact .inr (Row.isLin_ok hl η)
  | _, .lam M, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | lam hM hb =>
          refine CS_arr.2 (fun Oa a ha _ => ?_)
          have := CM.fp M hM hC.2.2 (hΓ.cons hC.1) η (ρ.cons a) (Own.envCons Oa Os) (hρ.cons ha)
          rw [sumL_cons_val ha, Own.add_comm] at this
          exact CS.mono _ this (Ok.le_trans (okOf_le_row hb η) (Ok.le_union_r _ _))
  | _, .app M v, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | app hM hv hd hc harr =>
          rw [sumL_union _ _ hd]
          simp only [Cmp.den]
          refine CS.mono _ (CS_arr.1 (CM.fp M hM harr hΓ η ρ Os hρ) _ _
            (VM.fp v hv harr.1 hΓ η ρ Os hρ) ?_) ?_
          · rcases hc with he | hl
            · exact .inl (sumL_empty he Os)
            · exact .inr (Row.isLin_ok hl η)
          · rw [← okOf_row]; exact okOf_union' η _ _
  | _, .force v, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | force hv hb => rw [okOf_row]; exact (VS_U.1 (VM.fp v hv ⟨hb, hC⟩ hΓ η ρ Os hρ)).2
  | _, .rcd M N, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | rcd hM hN =>
          exact CS_wth.2 ⟨(CM.fp M hM hC.1 hΓ η ρ Os hρ).mono_row (Row.sub_union_l _ _),
            (CM.fp N hN hC.2 hΓ η ρ Os hρ).mono_row (Row.sub_union_r _ _)⟩
  | _, .prj1 M, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with | prj1 hM hD => exact (CS_wth.1 (CM.fp M hM ⟨hC, hD⟩ hΓ η ρ Os hρ)).1
  | _, .prj2 M, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with | prj2 hM hC' => exact (CS_wth.1 (CM.fp M hM ⟨hC', hC⟩ hΓ η ρ Os hρ)).2
  | _, .split v M, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | split hv hM hd hA hB =>
          rw [sumL_union _ _ hd]
          obtain ⟨O₁, O₂, h12, h1, h2⟩ := VS_prod.1 (VM.fp v hv ⟨hA, hB⟩ hΓ η ρ Os hρ)
          simp only [Cmp.den]
          have := CM.fp M hM hC ((hΓ.cons hA).cons hB) η
            ((ρ.cons (v.den η ρ).1).cons (v.den η ρ).2)
            (Own.envCons O₂ (Own.envCons O₁ Os)) ((hρ.cons h1).cons h2)
          rw [sumL_cons_val h2, sumL_cons_val h1] at this
          rw [h12, show O₁ + O₂ + sumL Γ _ Os = O₂ + (O₁ + sumL Γ _ Os) by
            rw [Own.add_comm O₁ O₂, Own.add_assoc]]
          exact this
  | _, .case v M N, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | case hv hM hN hd hA hB =>
          rw [sumL_union _ _ hd]
          have hvs := VM.fp v hv ⟨hA, hB⟩ hΓ η ρ Os hρ
          simp only [Cmp.den]
          generalize v.den η ρ = x at hvs ⊢
          rcases x with a | b
          · have := CM.fp M hM hC (hΓ.cons hA) η (ρ.cons a) (Own.envCons _ Os)
              (hρ.cons (VS_inl.1 hvs))
            rw [sumL_cons_val (VS_inl.1 hvs)] at this
            exact this.mono_row (Row.sub_union_l _ _)
          · have := CM.fp N hN hC (hΓ.cons hB) η (ρ.cons b) (Own.envCons _ Os)
              (hρ.cons (VS_inr.1 hvs))
            rw [sumL_cons_val (VS_inr.1 hvs)] at this
            exact this.mono_row (Row.sub_union_r _ _)
  | _, .ite v M N, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | ite hv hM hN hd =>
          rw [sumL_union _ _ hd, VS_g.1 (VM.fp v hv trivial hΓ η ρ Os hρ), Own.zero_add]
          simp only [Cmp.den]
          cases (v.den η ρ : Bool)
          · exact (CM.fp N hN hC hΓ η ρ Os hρ).mono_row (Row.sub_union_r _ _)
          · exact (CM.fp M hM hC hΓ η ρ Os hρ).mono_row (Row.sub_union_l _ _)
  | _, .absurd v, _, _, _, _, _, η, ρ, _, _ => (v.den η ρ : Empty).elim
  | _, .prim p a b, _, _, h, _, hΓ, η, ρ, Os, hρ => by
      have key : ∀ {L₁ L₂ : VSet Γ}, VM L₁ a → VM L₂ b → L₁.Disj L₂ →
          CS (.F (.g p.res)) η.lv (okOf η Row.none) (sumL Γ (L₁.union L₂) Os)
            ((Cmp.prim p a b).den η ρ) :=
        fun ha hb hd => by
          rw [sumL_union _ _ hd, VS_g.1 (VM.fp a ha trivial hΓ η ρ Os hρ),
            VS_g.1 (VM.fp b hb trivial hΓ η ρ Os hρ), Own.zero_add]
          exact CS_F.2 (.ret (VS_g.2 rfl))
      cases p <;> cases h <;> exact key ‹_› ‹_› ‹_›
  | _, .emit v, _, _, h, _, hΓ, η, ρ, Os, hρ => by
      cases h with
      | emit hv =>
          rw [VS_g.1 (VM.fp v hv trivial hΓ η ρ Os hρ)]
          exact CS_F.2 (.act .out (fun _ => .ret (VS_g.2 rfl)))
  | _, .op x o v M, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | op _ _ hv hM hd hc =>
          rw [sumL_union _ _ hd, VS_g.1 (VM.fp v hv trivial hΓ η ρ Os hρ), Own.zero_add]
          simp only [Cmp.den]
          refine opA_safe _ (okOf_sub (Row.sub_union_l _ _) η _ _ (okOf_inst η x)) ?_ (fun y => ?_)
          · rcases hc with he | hl
            · rw [sumL_empty he]; exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => .nil⟩
            · exact CancelOK.lin hl
          · have := CM.fp M hM hC (hΓ.cons (A := .g _) trivial) η (ρ.cons (VTy.gv y)) (Own.envCons 0 Os)
              (hρ.cons (VS_g.2 rfl))
            rw [sumL_cons_false] at this
            exact this.mono_row (Row.sub_union_r _ _)
  | _, .ab x a v, _, _, h, _, hΓ, η, ρ, Os, hρ => by
      cases h with
      | ab _ _ hv =>
          rw [VS_g.1 (VM.fp v hv trivial hΓ η ρ Os hρ)]
          exact abA_safe _ (okOf_inst η x) .nil
  | _, .handle (A := A) e bk hr hop hab B, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | handle _ _ hB Rr hhr hRr Ro hhop hRo Ra hhab hRa hd hOH hfwd hsub hbk hA =>
          rw [sumL_union _ _ hd]
          simp only [Cmp.den]
          refine nuA_safe _ (fun i => ?_)
          have hB' := CS_F.1 (CM.fp B hB (VTy.Sc.mono (Nat.le_succ _) _ hA) hΓ.mono (η.cons i) ρ Os
            (hρ.ext (by rw [IEnv.lv_length]; exact hΓ) (i, e)))
          refine hnd_safe _ hB' ?_ ?_ ?_ (hOH.imp (sumL_empty · Os) id) ?_ ?_
            (Ok.le_trans (okOf_sub hsub η) (by rw [okOf_row]; exact Ok.le_refl _))
          · intro O' x hx
            rw [IEnv.lv_cons, VS_ext _ A (by rw [IEnv.lv_length]; exact hA)] at hx
            have := CM.fp hr hhr hC (hΓ.cons hA) η (ρ.cons x) (Own.envCons O' Os) (hρ.cons hx)
            rw [sumL_cons_val hx] at this
            exact this.mono_row (Row.sub_trans hRr (Row.sub_union_r _ _))
          · intro o v Oκ k d hκ
            have := CM.fp (hop o) (hhop o) hC ((hΓ.cons (A := .g _) trivial).cons (kty_sc hbk hC)) η
              ((ρ.cons (VTy.gv v)).cons _) (Own.envCons Oκ (Own.envCons 0 Os))
              ((hρ.cons (VS_g.2 rfl)).cons hκ)
            rw [sumL_cons_val hκ, sumL_cons_false, sumL_none, Own.add_zero] at this
            exact this.mono_row (Row.sub_trans (hRo o) (Row.sub_union_r _ _))
          · intro a v
            have := CM.fp (hab a) (hhab a) hC (hΓ.cons (A := .g _) trivial) η (ρ.cons (VTy.gv v))
              (Own.envCons 0 Os) (hρ.cons (VS_g.2 rfl))
            rw [sumL_cons_false] at this
            exact this.mono_row (Row.sub_trans (hRa a) (Row.sub_union_r _ _))
          · rcases hfwd with he | hl
            · exact .inl (sumL_empty he Os)
            · exact .inr (Row.isLin_tail η i hl)
          · intro j e' hne hj
            exact okOf_sub (Row.sub_union_l _ _) η _ _ ((okOf_cons _ η i j e' hj).resolve_right hne)
  | _, .handleAt x bk hr hop hab B, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | handleAt _ _ hB Rr hhr hRr Ro hhop hRo Ra hhab hRa hd hOH hfwd hsub hbk hA =>
          rw [sumL_union _ _ hd]
          simp only [Cmp.den]
          refine hnd_safe _ (CS_F.1 (CM.fp B hB hA hΓ η ρ Os hρ)) ?_ ?_ ?_
            (hOH.imp (sumL_empty · Os) id) ?_ ?_
            (Ok.le_trans (okOf_sub hsub η) (by rw [okOf_row]; exact Ok.le_refl _))
          · intro O' x hx
            have := CM.fp hr hhr hC (hΓ.cons hA) η (ρ.cons x) (Own.envCons O' Os) (hρ.cons hx)
            rw [sumL_cons_val hx] at this
            exact this.mono_row (Row.sub_trans hRr (Row.sub_union_r _ _))
          · intro o v Oκ k d hκ
            have := CM.fp (hop o) (hhop o) hC ((hΓ.cons (A := .g _) trivial).cons (kty_sc hbk hC)) η
              ((ρ.cons (VTy.gv v)).cons _) (Own.envCons Oκ (Own.envCons 0 Os))
              ((hρ.cons (VS_g.2 rfl)).cons hκ)
            rw [sumL_cons_val hκ, sumL_cons_false, sumL_none, Own.add_zero] at this
            exact this.mono_row (Row.sub_trans (hRo o) (Row.sub_union_r _ _))
          · intro a v
            have := CM.fp (hab a) (hhab a) hC (hΓ.cons (A := .g _) trivial) η (ρ.cons (VTy.gv v))
              (Own.envCons 0 Os) (hρ.cons (VS_g.2 rfl))
            rw [sumL_cons_false] at this
            exact this.mono_row (Row.sub_trans (hRa a) (Row.sub_union_r _ _))
          · rcases hfwd with he | hl
            · exact .inl (sumL_empty he Os)
            · exact .inr (fun j e' _ hj => Row.isLin_ok hl η j e' hj)
          · intro j e' _ hj
            exact okOf_sub (Row.sub_union_l _ _) η j e' hj
  | _, .nu e M, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | nu _ hM hz =>
          simp only [Cmp.den]
          refine nuA_safe _ (fun i => ?_)
          have := CM.fp M hM (CTy.Sc.mono (Nat.le_succ _) _ hC) hΓ.mono (η.cons i) ρ Os
            (hρ.ext (by rw [IEnv.lv_length]; exact hΓ) (i, e))
          rw [IEnv.lv_cons, CS_ext _ _ (by rw [IEnv.lv_length]; exact hC)] at this
          exact CS.mono _ this (okOf_cons_tail _ η i hz)
  | _, .ieq x y, _, _, h, _, _, η, ρ, Os, hρ => by
      cases h; rw [sumL_none]; exact CS_F.2 (.ret (VS_g.2 rfl))
  | _, .ilam (e := e) M, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | ilam hM =>
          refine CS_pi.2 (fun i => ?_)
          have := CM.fp M hM (CTy.Sc.mono (Nat.le_succ _) _ hC) hΓ.mono (η.cons i) ρ Os
            (hρ.ext (by rw [IEnv.lv_length]; exact hΓ) (i, e))
          rw [IEnv.lv_cons, CS_ext _ _ (by rw [IEnv.lv_length]; exact hC)] at this
          exact CS.mono _ this (okOf_cons _ η i)
  | _, .iapp (e := e) M x, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | iapp _ hM =>
          refine CS.mono _ (CS_pi.1 (CM.fp M hM hC hΓ η ρ Os hρ) (η _ x)) ?_
          intro j e' hj
          rcases hj with hj | ⟨rfl, rfl⟩
          · exact okOf_sub (Row.sub_union_l _ _) η _ _ hj
          · exact okOf_sub (Row.sub_union_r _ _) η _ _ (okOf_inst η x)
  | _, .newcap e s co v, _, _, h, _, hΓ, η, ρ, Os, hρ => by
      cases h with
      | newcap _ _ hv hnoab Rc hco =>
          rw [VS_g.1 (VM.fp v hv trivial hΓ η ρ Os hρ)]
          simp only [Cmp.den]
          refine CS_F.2 (.nuNew (fun n _ => .ret ?_))
          refine VS_cap.2 ⟨by simp [VTy.capv], hnoab, fun o a st => ?_⟩
          have := CM.fp (co o) (hco o) coRes_sc (by intro B z; rcases z with _ | _ | z <;>
              first | exact trivial | exact nomatch z) IEnv.nil
            ((Env.nil.cons (VTy.gv a)).cons (VTy.gv st))
            (fun _ _ => 0) (by intro B z; rcases z with _ | _ | z <;> first | exact VS_g.2 rfl |
              exact nomatch z)
          rw [sumL_none, okOf_nil] at this
          exact (CS_F.1 this).mapP (fun _ _ h => VS_coRes_zero h)
  | _, .getcap v, _, _, h, _, hΓ, η, ρ, Os, hρ => by
      cases h with
      | getcap hv =>
          obtain ⟨hO, _⟩ := VS_cap.1 (VM.fp v hv trivial hΓ η ρ Os hρ)
          simp only [Cmp.den]
          rw [hO, ← Own.zero_add (Own.one _ _)]
          exact CS_F.2 (.act .kill (fun _ => .ret (VS_g.2 rfl)))
  | _, .lend (e := e) (s := sg) (A := A) v M, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | lend hv hM hd hlin =>
          have hA : A.Sc Ψ.length := hC.2.1
          rw [sumL_union _ _ hd]
          obtain ⟨hO, hnoab, hco⟩ := VS_cap.1 (VM.fp v hv trivial hΓ η ρ Os hρ)
          simp only [Cmp.den]
          rw [hO]
          refine CS_F.2 (.act (.rd (by simp [Own.one])) (fun st => .nu (fun i => ?_)))
          have hM' := CS_F.1 (CM.fp M hM (VTy.Sc.mono (Nat.le_succ _) _ hA) hΓ.mono (η.cons i) ρ Os
            (hρ.ext (by rw [IEnv.lv_length]; exact hΓ) (i, e)))
          rw [IEnv.lv_cons, VS_ext _ A (by rw [IEnv.lv_length]; exact hA)] at hM'
          have hrun := runL_safe hM' (c := (v.den η ρ).1) (co := (v.den η ρ).2) hco hnoab
            (fun j e' hne hj => Row.isLin_tail η i hlin j e' hne hj)
            (Q := fun O x => ∃ O₁, O = O₁ + Own.one (.cap sg) (v.den η ρ).1 ∧
              VS (.sum A (.g .int)) η.lv O₁ x)
            (fun O x hx => ⟨O, rfl, VS_inl.2 hx⟩)
            (fun n => ⟨0, by simp, VS_inr.2 (VS_g.2 rfl)⟩) st
          have := TS.bind (F := 0) hrun
            (Q := fun O' a => VS (.prod (.cap e sg) (.sum A (.g .int))) η.lv O' a)
            (f := fun z => Tree.ret ((v.den η ρ), z))
            (fun O' z hz => by
              obtain ⟨O₁, rfl, hz⟩ := hz
              rw [Own.add_zero]
              exact .ret (VS_prod.2 ⟨_, _, Own.add_comm _ _, VS_cap.2 ⟨rfl, hnoab, hco⟩, hz⟩))
            (.inl rfl) (Ok.le_refl _)
          rw [Own.add_zero, Own.add_comm] at this
          exact this.mono (okOf_cons_rem _ η i)
  | _, .using ℓ M, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | «using» _ hM hc =>
          simp only [Cmp.den]
          refine CS_F.2 (.nuAcq (fun n _ => ?_))
          have hM' := CS_F.1 (CM.fp M hM (VTy.Sc.mono (Nat.le_succ _) _ hC) hΓ.mono (η.cons n) ρ Os
            (hρ.ext (by rw [IEnv.lv_length]; exact hΓ) (n, S.Res)))
          rw [IEnv.lv_cons, VS_ext _ _ (by rw [IEnv.lv_length]; exact hC)] at hM'
          refine (addFin_safe hM' (fun j e hne hj => ?_) ℓ).mono (okOf_cons_rem _ η n)
          exact Row.noC_ok hc η j e ((okOf_cons _ η n j e hj).resolve_right hne)
  | _, .unfold v, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | unfold hv hb =>
          have hA := hC.1.1
          have hs := VS_strm.1 (VM.fp v hv ⟨hb, hA⟩ hΓ η ρ Os hρ)
          simp only [Cmp.den]
          rw [okOf_row]
          generalize v.den η ρ = st at hs ⊢
          rcases st with ⟨p, d⟩
          have hu := hs.unf
          refine CS_wth.2 ⟨CS_F.2 (hu.1.mapP fun O x hx => ?_),
            CS_F.2 (hu.2.mapP fun O _ hx => VS_g.2 hx)⟩
          rcases x with a | ⟨n, st⟩
          · exact VS_inl.2 hx
          · exact VS_inr.2 (VS_prod.2 ⟨0, O, by simp, VS_g.2 rfl, VS_strm.2 hx⟩)
  | _, .bfix x a v n M, _, _, h, hC, hΓ, η, ρ, Os, hρ => by
      cases h with
      | bfix _ _ _ hv hM hsub hb =>
          rw [sumL_none]
          simp only [Cmp.den]
          induction n with
          | zero =>
              exact abA_safe _ (okOf_sub (Row.sub_union_l _ _) η _ _ (okOf_inst η x)) .nil
          | succ n ih =>
              have := CM.fp M hM hC (hΓ.cons ⟨hb, hC⟩) η (ρ.cons (VTy.uv _)) (Own.envCons 0 Os)
                (hρ.cons (VS_U.2 ⟨fun _ => rfl, CS.mono _ ih (okOf_le_row hsub η)⟩))
              rw [sumL_cons_false, sumL_none] at this
              exact this.mono_row (Row.sub_union_r _ _)
end

/-! ## Safety -/

/-- **Unary resource and effect safety** (`docs/effects-tr` T5.2, read on trees). A moded closed
program, run against the world with a ghost count of live tokens, never fails an action: every
free, read, write and consume finds its token, and every cell it touches is live. No operation
reaches the top: the program performs on no instance, and every operation inside it is handled
(effect safety). If it returns, nothing is live: every resource a `using` frame acquired was freed
exactly once (on return, on abort, when a continuation holding the frame was cancelled or a stream
was dropped), and every capability, lent or not, was consumed exactly once. -/
theorem safety {g : G} (P : Prog S g) {R : Row S []}
    (hP : CM (Ψ := []) (Γ := []) VSet.none R P) :
    (P.den IEnv.nil Env.nil).Safe (fun O _ => O = 0) ⟨Wd.init, 0⟩ := by
  have h := CM.fp P hP trivial (fun _ x => nomatch x) IEnv.nil Env.nil (fun _ _ => 0)
    (fun _ x => nomatch x)
  rw [okOf_nil] at h
  exact adequacyU ((CS_F.1 h).mapP (fun O _ hv => VS_g.1 hv)) _
    ⟨rfl, fun _ _ h0 => absurd rfl h0, fun _ _ _ => ⟨rfl, rfl⟩⟩

/-- The ghost run is the run: a checked action executes as the unchecked one does. -/
theorem Act.sexec_exec {g : G} (a : Act g) (s : SW) {y : g.den} {s' : SW}
    (h : a.sexec s = some (y, s')) : a.exec s.w = some (y, s'.w) := by
  obtain ⟨w, L⟩ := s
  cases a with
  | out n => simp only [Act.sexec, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | acq ℓ r => simp only [Act.sexec, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | use ℓ r => simp only [Act.sexec, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | free ℓ r =>
      simp only [Act.sexec] at h
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | new c v => simp only [Act.sexec, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | rd c g =>
      simp only [Act.sexec] at h
      split at h
      · cases h
      · simp only [Act.exec]
        cases hg : w.get c g with
        | none => rw [hg] at h; cases h
        | some v => rw [hg] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
                    obtain ⟨rfl, rfl⟩ := h; first | rfl | exact ⟨rfl, rfl⟩
  | wr c v =>
      simp only [Act.sexec] at h
      split at h
      · cases h
      · simp only [Act.exec]
        cases hg : w.store c with
        | none => rw [hg] at h; cases h
        | some u => rw [hg] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
                    obtain ⟨rfl, rfl⟩ := h; first | rfl | exact ⟨rfl, rfl⟩
  | kill c g =>
      simp only [Act.sexec] at h
      split at h
      · cases h
      · simp only [Act.exec]
        cases hg : w.get c g with
        | none => rw [hg] at h; cases h
        | some v => rw [hg] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
                    obtain ⟨rfl, rfl⟩ := h; first | rfl | exact ⟨rfl, rfl⟩

theorem Tree.Safe.obs {P : Own → X → Prop} (render : X → GV) :
    (t : Tree S X) → ∀ s, t.Safe P s → ∃ v, (t.obs render s.w).out = .ret v
  | .ret x, _, _ => ⟨render x, rfl⟩
  | .op .., _, h => h.elim
  | .ab .., _, h => h.elim
  | .nu k, s, h => by
      simp only [Tree.Safe] at h
      simp only [Tree.obs]
      exact Tree.Safe.obs render (k s.w.next) _ h
  | .act a k, s, h => by
      simp only [Tree.Safe] at h
      split at h
      · exact h.elim
      · rename_i y s' hs
        simp only [Tree.obs, Act.sexec_exec a s hs]
        exact Tree.Safe.obs render (k y) s' h

/-- **A moded closed program answers.** It is never stuck and never ends at an unhandled
operation. -/
theorem safety_obs {g : G} (P : Prog S g) {R : Row S []}
    (hP : CM (Ψ := []) (Γ := []) VSet.none R P) : ∃ v, P.obs.out = .ret v :=
  Tree.Safe.obs (G.render g) _ _ (safety P hP)

end EffRel
