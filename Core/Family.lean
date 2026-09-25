import Core.Splits

/-!
# Core — borrowing a family of places at one lifetime

A place-record is a tuple of owned references, one per leaf.  Borrowing it borrows every leaf,
and the callback receives the family of leaf borrows at **one** lifetime `'c`:

    withborF2 : Ref A ⊗ Ref B ⊸ (∀'c ⊏ ⊓Δ. Mut 'c A ⊗ Mut 'c B ⊸ ['c] T) ⊸ (Ref A ⊗ Ref B) ⊗ T
    withborF2 : Ref A ⊗ Ref B ⊸ (∀'c ⊏ ⊓Δ. Imm 'c A ⊗ Imm 'c B ⊸ ['c] T) ⊸ (Ref A ⊗ Ref B) ⊗ T

(`SPEC.md` §5's `withbor2`; here `withborF2`, since `withbor2` names the constant of the
paper's second `withbor` axiom in `CDerives`.)  The term is

    withborF2 ≜ λp. λg. let (x, y) = p;
                 let (x′, r) = withbor x (Λ. λmx.
                                 let (y′, t) = withbor y (Λ. λmy. g () (mx, my));
                                 (y′, t));
                 let (y′, t) = r; ((x′, y′), t)

and its typings are derived rules of `CDerives`, so `fundamentalC` covers them.  The outer
`withbor` borrows `x` at `'a ⊏ ⊓Δ`, the inner one `y` at `'b ⊏ 'a`; `⊑Mut` (`⊑Imm`) shortens
`mx` to `'b`, and the callback is instantiated at `'b` (`∀E`, `'b ⊏ ⊓Δ`).  `[]I` at `'a` boxes
`(y′, t)`, so `Δ, 'a ⊢ B ⊐ 'a` and `Δ, 'a ⊢ T ⊐ 'a` are premises (`hBo`, `hTo`).  `VOutlives`
has no rule at `U C` or `Unk`, so `B` and `T` hold neither outside `!`; they may hold `μ`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (entailsLt_of_bound interp_meet_left interp_meet_right)

/-! ### Types -/

/-- The family of leaf borrows at `@c`: `M @c A ⊗ M @c B`, `M` being `Mut` or `Imm`. -/
def famTy2 (M : Lifetime.Life → VTy → VTy) (c : Lifetime.Life) (A B : VTy) : VTy :=
  .tensor (M c A) (M c B)

/-- `∀'c ⊏ @bnd. F('c) ⊸ ['c] T`. -/
def cbTy2 (M : Lifetime.Life → VTy → VTy) (c : LifeVar) (bnd : Lifetime.Life) (A B T : VTy) :
    VTy :=
  .all c bnd (.lolli (famTy2 M (.var c) A B) (.box (.var c) T))

/-- `Ref A ⊗ Ref B`. -/
abbrev refs2 (A B : VTy) : VTy := .tensor (.ref A) (.ref B)

/-- `Ref A ⊗ Ref B ⊸ (∀'c ⊏ @bnd. F('c) ⊸ ['c] T) ⊸ (Ref A ⊗ Ref B) ⊗ T`. -/
def withborF2Ty (M : Lifetime.Life → VTy → VTy) (c : LifeVar) (bnd : Lifetime.Life)
    (A B T : VTy) : VTy :=
  .lolli (refs2 A B) (.lolli (cbTy2 M c bnd A B T) (.tensor (refs2 A B) T))

abbrev mutM : Lifetime.Life → VTy → VTy := .mut
abbrev immM : Lifetime.Life → VTy → VTy := .imm

/-! ### The term -/

/-- `Λ. λmy. g () (mx, my)`, with `mx` at index 2 and `g` at index 6. -/
def inner2 : Expr := lam2 (.app (.app (.var 6) unit') (.pair (.var 2) (.var 0)))

/-- `Λ. λmx. let (y′, t) = withbor y inner2; (y′, t)`, with `y` at index 2. -/
def outer2 : Expr :=
  lam2 (.letpair (.app (.app withbor (.var 2)) inner2) (.pair (.var 1) (.var 0)))

/-- `λp. λg. let (x, y) = p; let (x′, r) = withbor x outer2; let (y′, t) = r; ((x′, y′), t)`. -/
def withborF2 : Expr :=
  lam2 (.letpair (.var 1)
    (.letpair (.app (.app withbor (.var 1)) outer2)
      (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0)))))

/-! ### Lifetime facts -/

/-- `Δ, 'a ⊏ ⊓Δ`: the outer callback's context. -/
abbrev FD₁ (Δ : LifeCtx) (x : LifeVar) : LifeCtx := Δ.extend x Δ.meetOfDom

/-- `Δ, 'a ⊏ ⊓Δ, 'b ⊏ ⊓(Δ, 'a)`: the inner callback's context. -/
abbrev FD₂ (Δ : LifeCtx) (x y : LifeVar) : LifeCtx := (FD₁ Δ x).extend y (FD₁ Δ x).meetOfDom

/-- `'b ⊏ ⊓Δ`: the family's callback is instantiated at the inner lifetime. -/
theorem entailsLt_inner (Δ : LifeCtx) (x y : LifeVar) :
    (FD₂ Δ x y).EntailsLt (.var y) Δ.meetOfDom :=
  entailsLt_of_bound (u := (FD₁ Δ x).meetOfDom) (by simp [LifeCtx.find?_extend])
    fun _ _ h => interp_meet_right h

/-- `'b ⊑ 'a`: `⊑Mut`/`⊑Imm` shortens the outer borrow to the inner lifetime. -/
theorem entailsLe_inner (Δ : LifeCtx) (x y : LifeVar) :
    (FD₂ Δ x y).EntailsLe (.var y) (.var x) := by
  intro δ hδ
  obtain ⟨m, n, hm, hn, hlt⟩ := hδ y (FD₁ Δ x).meetOfDom (by simp [LifeCtx.find?_extend])
  obtain ⟨p, hp, hpn⟩ := interp_meet_left hn
  exact ⟨m, p, hm, hp, Nat.le_of_lt (Nat.lt_of_le_of_lt hpn hlt)⟩

theorem wf_var_self (Δ : LifeCtx) (x : LifeVar) (u : Lifetime.Life) :
    (Lifetime.Life.var x).wf (Δ.extend x u) = true := by
  simp [Lifetime.Life.wf, LifeCtx.find?_extend]

/-- `[]I`'s premise at a context of two live slots and a consumed rest. -/
theorem outlives_two {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {S T : VTy}
    (ha : Δ.Defines a) (hS : VOutlives Δ a S) (hT : VOutlives Δ a T) (h : Ctx.Dead Γ) :
    CtxOutlives Δ (⟨S, true⟩ :: ⟨T, true⟩ :: Γ) a := by
  refine ⟨ha, ?_⟩
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs
  · exact hS
  · exact (CtxOutlives.solo ha hT h).2 s hs hl

theorem VScoped.extend {Δ : LifeCtx} {A : VTy} (h : VScoped Δ A) (x : LifeVar) (u : Lifetime.Life) :
    VScoped (Δ.extend x u) A := by
  intro z hz
  obtain ⟨w, hw⟩ := h z hz
  rw [LifeCtx.find?_extend]
  split
  · exact ⟨u, rfl⟩
  · exact ⟨w, hw⟩

/-! ### Side conditions -/

/-- What a family at `M` needs of `CDerives`: `withbor` at `M` (with the side condition `side`:
form (2)'s `Δ ⊢ S ⊐ @b` at `Mut`, form (1)'s scoping at `Imm`) and `⊑M`. -/
structure Borrows (M : Lifetime.Life → VTy → VTy) (side : LifeCtx → VTy → Prop) : Prop where
  ax : ∀ {Δ : LifeCtx} {Γ : Ctx VTy} {S T₂ : VTy} (z : LifeVar), Ctx.Dead Γ → Δ.find? z = none →
    side Δ S → ¬ VFree z S → ¬ VFree z T₂ →
    CDerives Δ Γ withbor (.val (.lolli (.ref S)
      (.lolli (.all z Δ.meetOfDom (.lolli (M (.var z) S) (.box (.var z) T₂))) (.tensor (.ref S) T₂))))
  sub : ∀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life} {S : VTy},
    CDerives Δ Γ e (.val (M b S)) → Δ.EntailsLe a b → CDerives Δ Γ e (.val (M a S))
  free : ∀ z a S, VFree z (M a S) ↔ (a.mentions z = true ∨ VFree z S)

/-- Form (2) of `withbor` and `⊑Mut`. -/
theorem borrowsMut : Borrows mutM (fun Δ S => ∃ b, Δ.Defines b ∧ VOutlives Δ b S) :=
  ⟨fun z hΓ hz hs hf₁ hf₂ => .withbor2 z hΓ hz hs hf₁ hf₂, fun h hle => .mutSub h hle,
    fun _ _ _ => Iff.rfl⟩

/-- Form (1) of `withbor` and `⊑Imm`. -/
theorem borrowsImm : Borrows immM (fun Δ S => VScoped Δ S) :=
  ⟨fun z hΓ hz hs hf₁ hf₂ => .withbor1 z hΓ hz hs hf₁ hf₂, fun h hle => .immSub h hle,
    fun _ _ _ => Iff.rfl⟩

/-- The freshness and renaming facts of the derived rule, at the types it is used at. -/
structure FamSide (M : Lifetime.Life → VTy → VTy) (Δ : LifeCtx) (c x y : LifeVar)
    (A B T : VTy) : Prop where
  hΔ : Δ.Ok
  hx : Δ.find? x = none
  hy : Δ.find? y = none
  hxy : x ≠ y
  hAx : ¬ VFree x A
  hBx : ¬ VFree x B
  hTx : ¬ VFree x T
  hAy : ¬ VFree y A
  hBy : ¬ VFree y B
  hTy : ¬ VFree y T
  hcbx : ¬ VFree x (cbTy2 M c Δ.meetOfDom A B T)
  hcby : ¬ VFree y (cbTy2 M c Δ.meetOfDom A B T)
  /-- The callback's family and result are `'c`-generic: `∀E` at `'b` renames `'c` to `'b`. -/
  hinst : VTy.instLife c (.var y) (.lolli (famTy2 M (.var c) A B) (.box (.var c) T))
    = .lolli (famTy2 M (.var y) A B) (.box (.var y) T)

/-! ### The derived rules -/

section
variable {M : Lifetime.Life → VTy → VTy} {side : LifeCtx → VTy → Prop} {Δ : LifeCtx}
  {c x y : LifeVar} {A B T : VTy}

theorem FamSide.ok₁ (s : FamSide M Δ c x y A B T) : (FD₁ Δ x).Ok :=
  s.hΔ.extend s.hx (Lifetime.meetOfDomL_wf Δ.entries)

theorem FamSide.hy₁ (s : FamSide M Δ c x y A B T) : (FD₁ Δ x).find? y = none := by
  simp [LifeCtx.find?_extend, s.hxy, s.hy]

/-- The inner callback, at `Δ, 'a`: `g` is instantiated at `'b` and applied to `(mx, my)`,
with `mx` shortened from `'a` to `'b`. -/
theorem d_inner2 (bw : Borrows M side) (s : FamSide M Δ c x y A B T) {Γ : Ctx VTy}
    {S₁ S₂ S₃ : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives (FD₁ Δ x)
      (⟨M (.var x) A, true⟩ :: ⟨S₁, false⟩ :: ⟨S₂, false⟩ :: ⟨S₃, false⟩ ::
        ⟨cbTy2 M c Δ.meetOfDom A B T, true⟩ :: Γ)
      inner2 (.val (.all y (FD₁ Δ x).meetOfDom (.lolli (M (.var y) B) (.box (.var y) T)))) := by
  refine .thunkV rfl (.allI (S := .unit)
    (Lifetime.Life.mentions_false_of_wf s.hy₁ (Lifetime.meetOfDomL_wf _))
    (fun _ _ h => s.ok₁.bound_mentions_false s.hy₁ h) ?_ (.ret (.lamV ?_)))
  · intro t ht hl
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | ht
    · rw [bw.free]
      simp [Lifetime.Life.mentions, Ne.symm s.hxy, s.hAy]
    · simp at hl
    · simp at hl
    · simp at hl
    · exact s.hcby
    · exact dead_noLive hΓ (P := fun t => ¬ VFree y t.ty) t ht hl
  have key : ∀ {Γ' : Ctx VTy}, Ctx.Solo Γ' 6 (cbTy2 M c Δ.meetOfDom A B T) →
      CDerives (FD₂ Δ x y) Γ' (.app (.var 6) unit')
        (.val (.lolli (famTy2 M (.var y) A B) (.box (.var y) T))) := fun h => by
    have := CDerives.allEV (a := .var y) (.var h) (entailsLt_inner Δ x y)
    rwa [s.hinst] at this
  exact appW (pairW (bw.sub (.var (by csolo)) (entailsLe_inner Δ x y)) (.var (by csolo)))
    (key (by csolo))

/-- The outer callback, at `Δ`: the inner `withbor` borrows `y` at `'b`, and `[]I` at `'a`
boxes what it returns once `mx` and `g` are consumed. -/
theorem d_outer2 (bw : Borrows M side) (s : FamSide M Δ c x y A B T)
    (hsideB : side (FD₁ Δ x) B) (hBo : VOutlives (FD₁ Δ x) (.var x) B)
    (hTo : VOutlives (FD₁ Δ x) (.var x) T) {Γ : Ctx VTy} {S₁ S₂ : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ
      (⟨.ref B, true⟩ :: ⟨S₁, false⟩ :: ⟨cbTy2 M c Δ.meetOfDom A B T, true⟩ :: ⟨S₂, false⟩ :: Γ)
      outer2
      (.val (.all x Δ.meetOfDom (.lolli (M (.var x) A) (.box (.var x) (.tensor (.ref B) T))))) := by
  refine .thunkV rfl (.allI (S := .unit)
    (Lifetime.Life.mentions_false_of_wf s.hx (Lifetime.meetOfDomL_wf _))
    (fun _ _ h => s.hΔ.bound_mentions_false s.hx h) ?_ (.ret (.lamV ?_)))
  · intro t ht hl
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | rfl | ht
    · simpa [VFree] using s.hBx
    · simp at hl
    · exact s.hcbx
    · simp at hl
    · exact dead_noLive hΓ (P := fun t => ¬ VFree x t.ty) t ht hl
  exact letW (A := .ref B) (B := T)
    (appW (d_inner2 bw s (by cdead))
      (appW (.var (by csolo)) (bw.ax y (by cdead) s.hy₁ hsideB s.hBy s.hTy)))
    (.boxI (pairW (.var (by csolo)) (.var (by csolo)))
      (outlives_two (LifeCtx.defines_of_wf (wf_var_self _ _ _)) hTo (.ref hBo) (by cdead)))

/-- **The derived rule.**  `withborF2 : Ref A ⊗ Ref B ⊸ (∀'c ⊏ ⊓Δ. M 'c A ⊗ M 'c B ⊸ ['c] T) ⊸
(Ref A ⊗ Ref B) ⊗ T`, at `M = Mut` (`withborM2_wf`) and `M = Imm` (`withborI2_wf`). -/
theorem withborF2_wf (bw : Borrows M side) (s : FamSide M Δ c x y A B T) (hsideA : side Δ A)
    (hsideB : side (FD₁ Δ x) B) (hBo : VOutlives (FD₁ Δ x) (.var x) B)
    (hTo : VOutlives (FD₁ Δ x) (.var x) T) {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ withborF2 (.val (withborF2Ty M c Δ.meetOfDom A B T)) := by
  refine .lamV (.lamV ?_)
  exact letW (A := .ref A) (B := .ref B) (.var (by csolo)) <|
    letW (A := .ref A) (B := .tensor (.ref B) T)
      (appW (d_outer2 bw s hsideB hBo hTo (by cdead))
        (appW (.var (by csolo))
          (bw.ax x (by cdead) s.hx hsideA s.hAx (by simp [VFree, s.hBx, s.hTx])))) <|
    letW (A := .ref B) (B := T) (.var (by csolo)) <|
    pairW (pairW (.var (by csolo)) (.var (by csolo))) (.var (by csolo))

end

/-- The `Mut` family.  `A` needs `withbor` form (2)'s side condition at `Δ`; `B` and `T` need to
outlive the outer lifetime `'a`, which also gives `B` its form (2) side condition. -/
theorem withborM2_wf {Δ : LifeCtx} {c x y : LifeVar} {A B T : VTy}
    (s : FamSide mutM Δ c x y A B T) (hA : ∃ b, Δ.Defines b ∧ VOutlives Δ b A)
    (hBo : VOutlives (FD₁ Δ x) (.var x) B) (hTo : VOutlives (FD₁ Δ x) (.var x) T)
    {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ withborF2 (.val (withborF2Ty mutM c Δ.meetOfDom A B T)) :=
  withborF2_wf borrowsMut s hA ⟨.var x, LifeCtx.defines_of_wf (wf_var_self _ _ _), hBo⟩ hBo hTo hΓ

/-- The `Imm` family. -/
theorem withborI2_wf {Δ : LifeCtx} {c x y : LifeVar} {A B T : VTy}
    (s : FamSide immM Δ c x y A B T) (hA : VScoped Δ A) (hB : VScoped Δ B)
    (hBo : VOutlives (FD₁ Δ x) (.var x) B) (hTo : VOutlives (FD₁ Δ x) (.var x) T)
    {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ withborF2 (.val (withborF2Ty immM c Δ.meetOfDom A B T)) :=
  withborF2_wf borrowsImm s hA (hB.extend x _) hBo hTo hΓ

/-! ### Semantic typing: the Fundamental Property at the derivation -/

theorem withborM2_sem {Δ : LifeCtx} {c x y : LifeVar} {A B T : VTy}
    (s : FamSide mutM Δ c x y A B T) (hA : ∃ b, Δ.Defines b ∧ VOutlives Δ b A)
    (hBo : VOutlives (FD₁ Δ x) (.var x) B) (hTo : VOutlives (FD₁ Δ x) (.var x) T) :
    SemV Δ [] withborF2 (withborF2Ty mutM c Δ.meetOfDom A B T) :=
  fundamentalC (withborM2_wf s hA hBo hTo .nil)

theorem withborI2_sem {Δ : LifeCtx} {c x y : LifeVar} {A B T : VTy}
    (s : FamSide immM Δ c x y A B T) (hA : VScoped Δ A) (hB : VScoped Δ B)
    (hBo : VOutlives (FD₁ Δ x) (.var x) B) (hTo : VOutlives (FD₁ Δ x) (.var x) T) :
    SemV Δ [] withborF2 (withborF2Ty immM c Δ.meetOfDom A B T) :=
  fundamentalC (withborI2_wf s hA hB hBo hTo .nil)

end BoCa.Fig16.LogRel.Core

end
