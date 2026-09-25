import Records.Splits

/-!
# Borrowing a family of places at one lifetime

A place-record is a tuple of owned references, one per leaf.  Borrowing it borrows every leaf,
and the callback receives the family of leaf borrows at **one** lifetime `'c`:

    withborM2 : Ref A ⊗ Ref B ⊸ (∀'c ⊏ ⊓Δ. Mut 'c A ⊗ Mut 'c B ⊸ ['c] T) ⊸ (Ref A ⊗ Ref B) ⊗ T
    withborI2 : Ref A ⊗ Ref B ⊸ (∀'c ⊏ ⊓Δ. Imm 'c A ⊗ Imm 'c B ⊸ ['c] T) ⊸ (Ref A ⊗ Ref B) ⊗ T

Both are terms of the language, and their rules are derived rules of `DerivesWf`:

    withborM2 ≜ λp. λg. let (x, y) = p;
                 let (x′, r) = withbor x (Λ. λmx.
                                 let (y′, t) = withbor y (Λ. λmy. g () (mx, my));
                                 (y′, t));
                 let (y′, t) = r; ((x′, y′), t)

The outer `withbor` borrows `x` at `'a ⊏ ⊓Δ`, the inner one borrows `y` at `'b ⊏ 'a`
(its bound is `⊓(Δ, 'a)`).  `⊑Mut` (`⊑Imm`) shortens `mx : Mut 'a A` to `Mut 'b A`, so the
callback is instantiated at `'b` (`∀E`, since `'b ⊏ 'a ⊏ ⊓Δ`) with both borrows at `'b`.

The outer callback must return `['a] (Ref B ⊗ T)`.  `[]I` at `'a` is applied to `(y′, t)` after
`mx` and `g` are consumed, so its premise is `Δ, 'a ⊢ B ⊐ 'a` and `Δ, 'a ⊢ T ⊐ 'a`
(`hBo`, `hTo`).  No outlives rule covers `⊸`, `∀` or `Unk`, so this derivation does not cover
a `B` or `T` with one of those outside `!`.
-/

noncomputable section

namespace BoCa.Places
open BoCa BoCa.Lifetime BoCa.Programs BoCa.Records

/-! ## Types -/

/-- The family of leaf borrows at `@c`: `M @c A ⊗ M @c B`, `M` being `Mut` or `Imm`. -/
def famTy (M : Life → Ty → Ty) (c : Life) (A B : Ty) : Ty := .tensor (M c A) (M c B)

/-- `∀'c ⊏ @bnd. F('c) ⊸ ['c] T`. -/
def cbTy (M : Life → Ty → Ty) (c : LifeVar) (bnd : Life) (A B T : Ty) : Ty :=
  .all c bnd (.lolli (famTy M (.var c) A B) (.box (.var c) T))

/-- `Ref A ⊗ Ref B`. -/
abbrev refs (A B : Ty) : Ty := .tensor (.ref A) (.ref B)

/-- `Ref A ⊗ Ref B ⊸ (∀'c ⊏ @bnd. F('c) ⊸ ['c] T) ⊸ (Ref A ⊗ Ref B) ⊗ T`. -/
def withbor2Ty (M : Life → Ty → Ty) (c : LifeVar) (bnd : Life) (A B T : Ty) : Ty :=
  .lolli (refs A B) (.lolli (cbTy M c bnd A B T) (.tensor (refs A B) T))

abbrev mutM : Life → Ty → Ty := .mut
abbrev immM : Life → Ty → Ty := .imm

/-! ## The term

It is the same term for `Mut` and `Imm`: `withbor` is one term (`[CONF]` Fig. 15) with three
typings, and the two derived rules below use its forms (2) and (1). -/

/-- `Λ. λmy. g () (mx, my)`, with `mx` at index 2 and `g` at index 6. -/
def inner2 : Expr := lam (lam (app2 (.var 6) unit' (.pair (.var 2) (.var 0))))

/-- `Λ. λmx. let (y′, t) = withbor y inner2; (y′, t)`, with `y` at index 2. -/
def outer2 : Expr := lam (lam (.letpair (app2 withbor (.var 2) inner2) (.pair (.var 1) (.var 0))))

/-- `λp. λg. let (x, y) = p; let (x′, r) = withbor x outer2; let (y′, t) = r; ((x′, y′), t)`. -/
def withbor2 : Expr :=
  lam2 (.letpair (.var 1)
    (.letpair (app2 withbor (.var 1) outer2)
      (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0)))))

/-! ## Lifetime facts -/

/-- `Δ, 'a ⊏ ⊓Δ`: the outer callback's context. -/
abbrev D₁ (Δ : LifeCtx) (x : LifeVar) : LifeCtx := Δ.extend x Δ.meetOfDom

/-- `Δ, 'a ⊏ ⊓Δ, 'b ⊏ ⊓(Δ, 'a)`: the inner callback's context. -/
abbrev D₂ (Δ : LifeCtx) (x y : LifeVar) : LifeCtx := (D₁ Δ x).extend y (D₁ Δ x).meetOfDom

theorem meetOfDom_extend (Δ : LifeCtx) (x : LifeVar) (u : Life) :
    (Δ.extend x u).meetOfDom = .meet (.var x) Δ.meetOfDom := rfl

/-- `'b ⊏ ⊓Δ`: the family's callback is instantiated at the inner lifetime. -/
theorem entailsLt_inner (Δ : LifeCtx) (x y : LifeVar) :
    (D₂ Δ x y).EntailsLt (.var y) Δ.meetOfDom :=
  entailsLt_of_bound (u := (D₁ Δ x).meetOfDom) (by simp [LifeCtx.find?_extend])
    fun _ _ h => interp_meet_right h

/-- `'b ⊑ 'a`: `⊑Mut`/`⊑Imm` shortens the outer borrow to the inner lifetime. -/
theorem entailsLe_inner (Δ : LifeCtx) (x y : LifeVar) :
    (D₂ Δ x y).EntailsLe (.var y) (.var x) := by
  intro δ hδ
  obtain ⟨m, n, hm, hn, hlt⟩ := hδ y (D₁ Δ x).meetOfDom (by simp [LifeCtx.find?_extend])
  obtain ⟨p, hp, hpn⟩ := interp_meet_left hn
  exact ⟨m, p, hm, hp, Nat.le_of_lt (Nat.lt_of_le_of_lt hpn hlt)⟩

theorem wf_var_self (Δ : LifeCtx) (x : LifeVar) (u : Life) :
    (Life.var x).wf (Δ.extend x u) = true := by
  simp [Life.wf, LifeCtx.find?_extend]

theorem wf_var_extend {Δ : LifeCtx} {x y : LifeVar} {u : Life} (h : (Life.var x).wf Δ = true) :
    (Life.var x).wf (Δ.extend y u) = true := by
  simp only [Life.wf, LifeCtx.find?_extend] at h ⊢
  split <;> simp_all

theorem meetOfDom_wf (Δ : LifeCtx) : Δ.meetOfDom.wf Δ = true := meetOfDomL_wf Δ.entries

/-- `[]I`'s premise at a context of two live slots and a consumed rest. -/
theorem outlives_two {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} {S T : Ty} (ha : Δ.Defines a)
    (hS : OutlivesRules Δ a S) (hT : OutlivesRules Δ a T) (h : Ctx.Dead Γ) :
    Ctx.Outlives Δ (⟨S, true⟩ :: ⟨T, true⟩ :: Γ) a := by
  refine ⟨ha, ?_⟩
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs
  · exact hS
  · exact (Ctx.Outlives.solo ha hT h).2 s hs hl

/-! ## Side conditions

The side conditions of the derived rules, at the types the rule is used at.  `Side2 M Δ c x y A
B T` collects the scoping, freshness and substitution facts; each is a `Bool` equation or a
fact about variable names, discharged by `rfl`/`decide` at concrete types. -/

structure Side2 (M : Life → Ty → Ty) (Δ : LifeCtx) (c x y : LifeVar) (A B T : Ty) : Prop where
  hx : Δ.find? x = none
  hy : Δ.find? y = none
  hxy : x ≠ y
  hcx : c ≠ x
  hcy : c ≠ y
  hA : A.scopedB Δ = true
  hB : B.scopedB Δ = true
  hT : T.scopedB Δ = true
  hAx : A.bindsB x = false
  hBx : B.bindsB x = false
  hTx : T.bindsB x = false
  hAy : A.bindsB y = false
  hBy : B.bindsB y = false
  hTy : T.bindsB y = false
  /-- The callback's family and result are `'c`-generic: `∀E` at `'b` renames `'c` to `'b`. -/
  hinst : Ty.instLife c (.var y) (.lolli (famTy M (.var c) A B) (.box (.var c) T))
    = .lolli (famTy M (.var y) A B) (.box (.var y) T)
  /-- `cbTy` is scoped in `Δ` (its binder `'c` fresh, its body scoped under `'c`). -/
  hcb : (cbTy M c Δ.meetOfDom A B T).scopedB Δ = true
  /-- `M` is `Mut` or `Imm`: scoping and binders are those of the payload. -/
  hMs : ∀ Δ' a S, (M a S).scopedB Δ' = (a.wf Δ' && S.scopedB Δ')
  hMb : ∀ a S z, (M a S).bindsB z = S.bindsB z

theorem Side2.cbBinds {M : Life → Ty → Ty} {Δ : LifeCtx} {c x y : LifeVar} {A B T : Ty}
    (s : Side2 M Δ c x y A B T) (z : LifeVar) (hz : c ≠ z) (hA : A.bindsB z = false)
    (hB : B.bindsB z = false) (hT : T.bindsB z = false) :
    (cbTy M c Δ.meetOfDom A B T).bindsB z = false := by
  simp [cbTy, famTy, Ty.bindsB, s.hMb, hA, hB, hT, hz]

/-! ## The derived rules -/

/-- `withbor`'s type at `M`: form (2) at `Mut`, form (1) at `Imm`. -/
def axTy (M : Life → Ty → Ty) (z : LifeVar) (bnd : Life) (S T₂ : Ty) : Ty :=
  .lolli (.ref S) (.lolli (.all z bnd (.lolli (M (.var z) S) (.box (.var z) T₂))) (.tensor (.ref S) T₂))

/-- What a family at `M` needs of the library: `withbor` at `M` (with the side condition
`side`, form (2)'s `Δ ⊢ S ⊐ @b` at `Mut`, nothing at `Imm`) and `⊑M`. -/
structure Borrows (M : Life → Ty → Ty) (side : LifeCtx → Ty → Prop) : Prop where
  ax : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {S T₂ : Ty} (z : LifeVar), Ctx.Dead Γ → Δ.find? z = none →
    side Δ S → (axTy M z Δ.meetOfDom S T₂).scopedB Δ = true →
    DerivesWf Δ Γ withbor (axTy M z Δ.meetOfDom S T₂)
  sub : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {a b : Life} {S : Ty},
    DerivesWf Δ Γ e (M b S) → Δ.EntailsLe a b → DerivesWf Δ Γ e (M a S)

/-- Form (2) of `withbor` and `⊑Mut`. -/
theorem borrowsMut : Borrows mutM (fun Δ S => ∃ b, Δ.Defines b ∧ Outlives Δ S b) :=
  ⟨fun z hΓ hz hs hwf => .withbor2Ax hΓ z hz hs hwf, fun h hle => .mutSub h hle⟩

/-- Form (1) of `withbor` and `⊑Imm`. -/
theorem borrowsImm : Borrows immM (fun _ _ => True) :=
  ⟨fun z hΓ hz _ hwf => .withbor1Ax hΓ z hz hwf, fun h hle => .immSub h hle⟩

section
variable {M : Life → Ty → Ty} {side : LifeCtx → Ty → Prop} {Δ : LifeCtx} {c x y : LifeVar}
  {A B T : Ty}

/-- The inner callback, at `Δ, 'a, 'b`: `g` is instantiated at `'b` and applied to
`(mx, my)`, with `mx` shortened from `'a` to `'b`. -/
theorem d_inner2 (bw : Borrows M side) (s : Side2 M Δ c x y A B T) {Γ : Ctx Ty} {S₁ S₂ S₃ : Ty}
    (hΓ : Ctx.Dead Γ) :
    DerivesWf (D₁ Δ x)
      (⟨M (.var x) A, true⟩ :: ⟨S₁, false⟩ :: ⟨S₂, false⟩ :: ⟨S₃, false⟩ ::
        ⟨cbTy M c Δ.meetOfDom A B T, true⟩ :: Γ)
      inner2 (.all y (D₁ Δ x).meetOfDom (.lolli (M (.var y) B) (.box (.var y) T))) := by
  have hy₁ : (D₁ Δ x).find? y = none := by
    simp [LifeCtx.find?_extend, s.hxy, s.hy]
  refine .allI (S := .unit) hy₁ (meetOfDom_wf _) ?_ ?_
  · intro t ht hl
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | ht
    · simp [s.hMb, s.hAy]
    · simp at hl
    · simp at hl
    · simp at hl
    · exact s.cbBinds y s.hcy s.hAy s.hBy s.hTy
    · exact Ctx.Dead.noBinds hΓ y t ht hl
  refine .lolliI ?_ ?_
  · rw [s.hMs]; simp [wf_var_self, Ty.scopedB_extend s.hBy (Ty.scopedB_extend s.hBx s.hB)]
  have hg := DerivesWf.allE (Δ := D₂ Δ x y) (a := .var y)
    (DerivesWf.var (Γ := (part (.pair (.var 2) (.var 0)) 0
      (⟨M (.var y) B, true⟩ :: ⟨.unit, false⟩ :: ⟨M (.var x) A, true⟩ :: ⟨S₁, false⟩ ::
        ⟨S₂, false⟩ :: ⟨S₃, false⟩ :: ⟨cbTy M c Δ.meetOfDom A B T, true⟩ :: Γ)).2)
      (i := 6) (T := cbTy M c Δ.meetOfDom A B T) (by solo)) (entailsLt_inner Δ x y)
  rw [cbTy, s.hinst] at hg
  exact appW (pairW (bw.sub (.var (by solo)) (entailsLe_inner Δ x y)) (.var (by solo))) hg

theorem Side2.scoped₁ (_ : Side2 M Δ c x y A B T) {S : Ty} (hS : S.scopedB Δ = true)
    (hx : S.bindsB x = false) : S.scopedB (D₁ Δ x) = true := Ty.scopedB_extend hx hS

theorem Side2.scoped₂ (s : Side2 M Δ c x y A B T) {S : Ty} (hS : S.scopedB Δ = true)
    (hx : S.bindsB x = false) (hy : S.bindsB y = false) : S.scopedB (D₂ Δ x y) = true :=
  Ty.scopedB_extend hy (s.scoped₁ hS hx)

/-- The outer callback, at `Δ, 'a`: the inner `withbor` borrows `y` at `'b`, and `[]I` at `'a`
boxes what it returns once `mx` and `g` are consumed. -/
theorem d_outer2 (bw : Borrows M side) (s : Side2 M Δ c x y A B T)
    (hsideB : side (D₁ Δ x) B) (hBo : OutlivesRules (D₁ Δ x) (.var x) B)
    (hTo : OutlivesRules (D₁ Δ x) (.var x) T) {Γ : Ctx Ty} {S₁ S₂ : Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ
      (⟨.ref B, true⟩ :: ⟨S₁, false⟩ :: ⟨cbTy M c Δ.meetOfDom A B T, true⟩ :: ⟨S₂, false⟩ :: Γ)
      outer2 (.all x Δ.meetOfDom (.lolli (M (.var x) A) (.box (.var x) (.tensor (.ref B) T)))) := by
  have hy₁ : (D₁ Δ x).find? y = none := by
    simp [LifeCtx.find?_extend, s.hxy, s.hy]
  refine .allI (S := .unit) s.hx (meetOfDom_wf _) ?_ ?_
  · intro t ht hl
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | rfl | ht
    · simp [Ty.bindsB, s.hBx]
    · simp at hl
    · exact s.cbBinds x s.hcx s.hAx s.hBx s.hTx
    · simp at hl
    · exact Ctx.Dead.noBinds hΓ x t ht hl
  refine .lolliI ?_ ?_
  · rw [s.hMs]; simp [wf_var_self, s.scoped₁ s.hA s.hAx]
  have hwf : (axTy M y (D₁ Δ x).meetOfDom B T).scopedB (D₁ Δ x) = true := by
    simp only [axTy, Ty.scopedB, s.hMs, Bool.and_eq_true, wf_var_self, meetOfDom_wf, hy₁,
      s.scoped₁ s.hB s.hBx, s.scoped₁ s.hT s.hTx, s.scoped₂ s.hB s.hBx s.hBy,
      s.scoped₂ s.hT s.hTx s.hTy, Option.isNone_none, and_self]
  exact letW (T₁ := .ref B) (T₂ := T) (by simp [Ty.scopedB, s.scoped₁ s.hB s.hBx, s.scoped₁ s.hT s.hTx])
    (appW (d_inner2 bw s (by dead)) (appW (.var (by solo)) (bw.ax y (by dead) hy₁ hsideB hwf)))
    (.boxIctx (pairW (.var (by solo)) (.var (by solo)))
      (outlives_two (LifeCtx.defines_of_wf (wf_var_self _ _ _)) hTo (.ref hBo) (by dead)))

/-- **The derived rule.**  `withbor2 : Ref A ⊗ Ref B ⊸ (∀'c ⊏ ⊓Δ. M 'c A ⊗ M 'c B ⊸ ['c] T) ⊸
(Ref A ⊗ Ref B) ⊗ T`, at `M = Mut` (`withborM2_wf`) and `M = Imm` (`withborI2_wf`). -/
theorem withbor2_wf (bw : Borrows M side) (s : Side2 M Δ c x y A B T) (hsideA : side Δ A)
    (hsideB : side (D₁ Δ x) B) (hBo : OutlivesRules (D₁ Δ x) (.var x) B)
    (hTo : OutlivesRules (D₁ Δ x) (.var x) T) {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ withbor2 (withbor2Ty M c Δ.meetOfDom A B T) := by
  have hwf : (axTy M x Δ.meetOfDom A (.tensor (.ref B) T)).scopedB Δ = true := by
    simp only [axTy, Ty.scopedB, s.hMs, Bool.and_eq_true, wf_var_self, meetOfDom_wf, s.hx,
      s.hA, s.hB, s.hT, s.scoped₁ s.hA s.hAx, s.scoped₁ s.hB s.hBx, s.scoped₁ s.hT s.hTx,
      Option.isNone_none, and_self]
  refine .lolliI (by simp [Ty.scopedB, s.hA, s.hB]) (.lolliI s.hcb ?_)
  exact letW (T₁ := .ref A) (T₂ := .ref B) (by simp [Ty.scopedB, s.hA, s.hB]) (.var (by solo)) <|
    letW (T₁ := .ref A) (T₂ := .tensor (.ref B) T) (by simp [Ty.scopedB, s.hA, s.hB, s.hT])
      (appW (d_outer2 bw s hsideB hBo hTo (by dead))
        (appW (.var (by solo)) (bw.ax x (by dead) s.hx hsideA hwf))) <|
    letW (T₁ := .ref B) (T₂ := T) (by simp [Ty.scopedB, s.hB, s.hT]) (.var (by solo)) <|
    pairW (pairW (.var (by solo)) (.var (by solo))) (.var (by solo))

end

/-- `withborM2`: the `Mut` family.  `A` needs `withbor` form (2)'s side condition at `Δ`;
`B` and `T` need to outlive the outer lifetime `'a`, which also gives `B` its form (2) side
condition. -/
theorem withborM2_wf {Δ : LifeCtx} {c x y : LifeVar} {A B T : Ty}
    (s : Side2 mutM Δ c x y A B T) (hA : ∃ b, Δ.Defines b ∧ Outlives Δ A b)
    (hBo : OutlivesRules (D₁ Δ x) (.var x) B) (hTo : OutlivesRules (D₁ Δ x) (.var x) T)
    {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ withbor2 (withbor2Ty mutM c Δ.meetOfDom A B T) :=
  withbor2_wf borrowsMut s hA ⟨.var x, LifeCtx.defines_of_wf (wf_var_self _ _ _), hBo⟩ hBo hTo hΓ

/-- `withborI2`: the `Imm` family. -/
theorem withborI2_wf {Δ : LifeCtx} {c x y : LifeVar} {A B T : Ty}
    (s : Side2 immM Δ c x y A B T)
    (hBo : OutlivesRules (D₁ Δ x) (.var x) B) (hTo : OutlivesRules (D₁ Δ x) (.var x) T)
    {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ withbor2 (withbor2Ty immM c Δ.meetOfDom A B T) :=
  withbor2_wf borrowsImm s trivial trivial hBo hTo hΓ

/-! ## Semantic typing

The derived rules are `DerivesWf` derivations, so the Fundamental Property
(`Fig16.LogRel.Typed.fundamentalProperty`, `[TR]` 6.151 at `SemX`) gives their semantic typing
with no new case: the compatibility lemma of each family is the Fundamental Property at the
derivation. -/

theorem withborM2_sem {Δ : LifeCtx} {c x y : LifeVar} {A B T : Ty}
    (s : Side2 mutM Δ c x y A B T) (hA : ∃ b, Δ.Defines b ∧ Outlives Δ A b)
    (hBo : OutlivesRules (D₁ Δ x) (.var x) B) (hTo : OutlivesRules (D₁ Δ x) (.var x) T)
    (hΔ : Δ.Ok) :
    Fig16.LogRel.Typed.SemX Δ [] withbor2 (withbor2Ty mutM c Δ.meetOfDom A B T) :=
  Fig16.LogRel.Typed.fundamentalProperty _ _ _ _ (withborM2_wf s hA hBo hTo .nil) hΔ
    (fun _ hs => absurd hs (by simp))

theorem withborI2_sem {Δ : LifeCtx} {c x y : LifeVar} {A B T : Ty}
    (s : Side2 immM Δ c x y A B T)
    (hBo : OutlivesRules (D₁ Δ x) (.var x) B) (hTo : OutlivesRules (D₁ Δ x) (.var x) T)
    (hΔ : Δ.Ok) :
    Fig16.LogRel.Typed.SemX Δ [] withbor2 (withbor2Ty immM c Δ.meetOfDom A B T) :=
  Fig16.LogRel.Typed.fundamentalProperty _ _ _ _ (withborI2_wf s hBo hTo .nil) hΔ
    (fun _ hs => absurd hs (by simp))

end BoCa.Places

end
